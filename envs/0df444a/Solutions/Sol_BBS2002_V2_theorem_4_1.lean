-- Prove2me | solution 1 for BBS2002.V2.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:54:56.128843+00:00
-- url     : https://prove2.me/submissions/3a1ed386-6405-4d60-9b20-5ad1eef0756c

import Definitions.Def_BBS2002_Arithmetic
import Definitions.Def_BBS2002_V2_Realizability

/- Local checked proof module: Helpers -/

namespace BBS2002

theorem AssumpVar.bne_self (u : AssumpVar) : (u != u) = false := by
  simp [bne]

theorem mem_eraseDups_of_mem {α : Type} [BEq α] {x : α} (l : List α) :
    x ∈ l.eraseDups → x ∈ l := by
  match l with
  | [] => intro h; cases h
  | a :: as =>
      simp only [List.eraseDups_cons, List.mem_cons]
      intro h
      rcases h with rfl | h
      · exact .inl rfl
      · exact .inr (List.mem_filter.mp (mem_eraseDups_of_mem _ h)).1
termination_by l.length
decreasing_by
  simp_wf
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem mem_eraseDups_of_mem' {α : Type} [DecidableEq α] {x : α} (l : List α) :
    x ∈ l → x ∈ l.eraseDups := by
  match l with
  | [] => intro h; cases h
  | a :: as =>
      simp only [List.mem_cons, List.eraseDups_cons]
      intro h
      by_cases hxa : x = a
      · exact .inl hxa
      · rcases h with rfl | h
        · exact absurd rfl hxa
        · have hfilt : x ∈ as.filter (fun b => !b == a) := by
            rw [List.mem_filter]
            exact ⟨h, by simp [hxa]⟩
          exact .inr (mem_eraseDups_of_mem' _ hfilt)
termination_by l.length
decreasing_by
  simp_wf
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem mem_eraseDups_iff {α : Type} [DecidableEq α] {x : α} {l : List α} :
    x ∈ l.eraseDups ↔ x ∈ l :=
  ⟨mem_eraseDups_of_mem l, mem_eraseDups_of_mem' l⟩

theorem freeAssumpVars_eq_nil_of_forall_not_mem {M : ProofTerm}
    (h : ∀ v ∈ freeAssumpVars M, False) : freeAssumpVars M = [] := by
  cases hm : freeAssumpVars M with
  | nil => rfl
  | cons v vs =>
      exfalso
      apply h v
      rw [hm]
      exact List.Mem.head _

theorem mem_freeAssumpVars_appAssump {M N : ProofTerm} {v : AssumpVar} :
    v ∈ freeAssumpVars (.appAssump M N) ↔
      v ∈ freeAssumpVars M ∨ v ∈ freeAssumpVars N := by
  simp only [freeAssumpVars, mem_eraseDups_iff, List.mem_append]

theorem mem_freeAssumpVars_lamAssump {u : AssumpVar} {M : ProofTerm} {v : AssumpVar} :
    v ∈ freeAssumpVars (.lamAssump u M) ↔ v ∈ freeAssumpVars M ∧ v ≠ u := by
  simp only [freeAssumpVars, List.mem_filter, bne_iff_ne]

theorem maxVarIdTerm_ge_of_mem_allVars (r : Term) (v : Var) (h : v ∈ allVarsTerm r) :
    v.id ≤ maxVarIdTerm r := by
  induction r with
  | var x =>
      simp only [allVarsTerm, List.mem_singleton] at h
      subst h
      exact Nat.le_refl _
  | const _ => cases h
  | lam x body ih =>
      simp only [allVarsTerm, List.mem_cons] at h
      simp only [maxVarIdTerm]
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)
  | app t s iht ihs =>
      simp only [allVarsTerm, List.mem_append] at h
      simp only [maxVarIdTerm]
      rcases h with h | h
      · exact Nat.le_trans (iht h) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ihs h) (Nat.le_max_right _ _)

theorem not_mem_allVarsTerm_of_gt (r : Term) (v : Var) (h : maxVarIdTerm r < v.id) :
    v ∉ allVarsTerm r := by
  intro hm
  have hle := maxVarIdTerm_ge_of_mem_allVars r v hm
  omega

theorem maxVarIdFormula_ge_of_mem_allVars (A : Formula) (v : Var) (h : v ∈ allVarsFormula A) :
    v.id ≤ maxVarIdFormula A := by
  induction A with
  | bot | varX => cases h
  | atom t => exact maxVarIdTerm_ge_of_mem_allVars t v h
  | imp B C ihB ihC =>
      simp only [allVarsFormula, List.mem_append] at h
      simp only [maxVarIdFormula]
      rcases h with h | h
      · exact Nat.le_trans (ihB h) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ihC h) (Nat.le_max_right _ _)
  | all x B ih =>
      simp only [allVarsFormula, List.mem_cons] at h
      simp only [maxVarIdFormula]
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem not_mem_allVarsFormula_of_gt (A : Formula) (v : Var) (h : maxVarIdFormula A < v.id) :
    v ∉ allVarsFormula A := by
  intro hm
  have hle := maxVarIdFormula_ge_of_mem_allVars A v hm
  omega

theorem mem_freeVarOccurrences_of_mem_allVars {r : Term} {v : Var}
    (h : v ∈ freeVarOccurrences r) : v ∈ allVarsTerm r := by
  induction r with
  | var x => exact h
  | const _ => cases h
  | lam x body ih =>
      simp only [freeVarOccurrences, List.mem_filter] at h
      exact List.Mem.tail _ (ih h.1)
  | app t s iht ihs =>
      simp only [freeVarOccurrences, allVarsTerm, List.mem_append] at h ⊢
      rcases h with h | h
      · exact .inl (iht h)
      · exact .inr (ihs h)

theorem mem_freeVarOccurrences_renameFreeVar (r : Term) (v v' z : Var)
    (hz : z ∈ freeVarOccurrences (renameFreeVar r v v')) :
    z ∈ freeVarOccurrences r ∨ z = v' := by
  induction r with
  | var x =>
      simp only [renameFreeVar] at hz
      split at hz
      · simp only [freeVarOccurrences, List.mem_singleton] at hz
        exact .inr hz
      · simp only [freeVarOccurrences, List.mem_singleton] at hz ⊢
        exact .inl hz
  | const _ => cases hz
  | lam x body ih =>
      simp only [renameFreeVar] at hz
      split at hz
      · exact .inl hz
      · simp only [freeVarOccurrences, List.mem_filter, bne_iff_ne] at hz ⊢
        rcases ih hz.1 with h1 | rfl
        · exact .inl ⟨h1, hz.2⟩
        · exact .inr rfl
  | app t s iht ihs =>
      simp only [renameFreeVar, freeVarOccurrences, List.mem_append] at hz ⊢
      rcases hz with hz | hz
      · rcases iht hz with h1 | rfl
        · exact .inl (.inl h1)
        · exact .inr rfl
      · rcases ihs hz with h1 | rfl
        · exact .inl (.inr h1)
        · exact .inr rfl

theorem substTerm_alphaEq_of_not_free (r : Term) (x : Var) (s : Term)
    (hx : x ∉ freeVarOccurrences r) :
    AlphaEqTerm (substTerm r x s) r := by
  match r with
  | .var v =>
      rw [substTerm.eq_def]
      have hvx : (v == x) = false := by
        simp only [beq_eq_false_iff_ne]
        intro h; subst h; exact hx (List.Mem.head _)
      simp only [hvx, Bool.false_eq_true, ↓reduceIte]
      exact AlphaEqTerm.refl _
  | .const c =>
      rw [substTerm.eq_def]
      exact AlphaEqTerm.refl _
  | .lam v body =>
      rw [substTerm.eq_def]
      by_cases hvx : v = x
      · simp only [hvx, beq_self_eq_true, ↓reduceIte]
        exact AlphaEqTerm.refl _
      · have hvxb : (v == x) = false := beq_eq_false_iff_ne.mpr hvx
        have hx_body : x ∉ freeVarOccurrences body := by
          intro hmem
          apply hx
          simp only [freeVarOccurrences, List.mem_filter, bne_iff_ne]
          exact ⟨hmem, Ne.symm hvx⟩
        simp only [hvxb, Bool.false_eq_true, ↓reduceIte]
        split
        · next hvs =>
          let freshId := Nat.max (maxVarIdTerm body) (Nat.max (maxVarIdTerm s) x.id) + 1
          let v' : Var := ⟨freshId, v.ty⟩
          have hle1 : maxVarIdTerm body ≤ Nat.max (maxVarIdTerm body) (Nat.max (maxVarIdTerm s) x.id) :=
            Nat.le_max_left _ _
          have hle2 : x.id ≤ Nat.max (maxVarIdTerm body) (Nat.max (maxVarIdTerm s) x.id) :=
            Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
          have hv'_not_all : v' ∉ allVarsTerm body := by
            apply not_mem_allVarsTerm_of_gt
            change maxVarIdTerm body < freshId
            omega
          have hv'_ne_x : x ≠ v' := by
            intro h; have := congrArg Var.id h; change x.id = freshId at this; omega
          have hx_ren : x ∉ freeVarOccurrences (renameFreeVar body v v') := by
            intro hmem
            rcases mem_freeVarOccurrences_renameFreeVar body v v' x hmem with h1 | h2
            · exact hx_body h1
            · exact hv'_ne_x h2
          have ih := substTerm_alphaEq_of_not_free (renameFreeVar body v v') x s hx_ren
          exact AlphaEqTerm.trans
            (AlphaEqTerm.lam_congr v' ih)
            (AlphaEqTerm.symm (AlphaEqTerm.lam_rename v v' body rfl (.inr hv'_not_all)))
        · next hvs =>
          exact AlphaEqTerm.lam_congr v (substTerm_alphaEq_of_not_free body x s hx_body)
  | .app t u =>
      rw [substTerm.eq_def]
      simp only [freeVarOccurrences, List.mem_append, not_or] at hx
      exact AlphaEqTerm.app
        (substTerm_alphaEq_of_not_free t x s hx.1)
        (substTerm_alphaEq_of_not_free u x s hx.2)
termination_by rawSize r
decreasing_by
  all_goals
    simp_wf
    simp [rawSize, renameFreeVar_rawSize]
    try omega

/-- Free variable occurrences in a formula `A` (without `eraseDups`). -/
def freeVarOccurrencesFormula : Formula → List Var
  | .bot | .varX => []
  | .atom t => freeVarOccurrences t
  | .imp A B => freeVarOccurrencesFormula A ++ freeVarOccurrencesFormula B
  | .all x A => (freeVarOccurrencesFormula A).filter (· != x)

theorem mem_freeVarOccurrencesFormula_of_mem_allVars {A : Formula} {v : Var}
    (h : v ∈ freeVarOccurrencesFormula A) : v ∈ allVarsFormula A := by
  induction A with
  | bot | varX => cases h
  | atom t => exact mem_freeVarOccurrences_of_mem_allVars h
  | imp B C ihB ihC =>
      simp only [freeVarOccurrencesFormula, allVarsFormula, List.mem_append] at h ⊢
      rcases h with h | h
      · exact .inl (ihB h)
      · exact .inr (ihC h)
  | all x B ih =>
      simp only [freeVarOccurrencesFormula, List.mem_filter] at h
      exact List.Mem.tail _ (ih h.1)

theorem mem_freeVarOccurrencesFormula_rename (A : Formula) (v v' z : Var)
    (hz : z ∈ freeVarOccurrencesFormula (renameFreeVarFormula A v v')) :
    z ∈ freeVarOccurrencesFormula A ∨ z = v' := by
  induction A with
  | bot | varX => cases hz
  | atom t => exact mem_freeVarOccurrences_renameFreeVar t v v' z hz
  | imp B C ihB ihC =>
      simp only [renameFreeVarFormula, freeVarOccurrencesFormula, List.mem_append] at hz ⊢
      rcases hz with hz | hz
      · rcases ihB hz with h1 | rfl
        · exact .inl (.inl h1)
        · exact .inr rfl
      · rcases ihC hz with h1 | rfl
        · exact .inl (.inr h1)
        · exact .inr rfl
  | all x B ih =>
      simp only [renameFreeVarFormula] at hz
      split at hz
      · exact .inl hz
      · simp only [freeVarOccurrencesFormula, List.mem_filter, bne_iff_ne] at hz ⊢
        rcases ih hz.1 with h1 | rfl
        · exact .inl ⟨h1, hz.2⟩
        · exact .inr rfl

theorem substFormula_betaREq_of_not_free (A : Formula) (x : Var) (t : Term)
    (hx : x ∉ freeVarOccurrencesFormula A) :
    FormulaBetaREq (substFormula A x t) A := by
  match A with
  | .bot =>
      rw [substFormula.eq_def]
      exact FormulaBetaREq.bot
  | .varX =>
      rw [substFormula.eq_def]
      exact FormulaBetaREq.varX
  | .atom s =>
      rw [substFormula.eq_def]
      exact FormulaBetaREq.atom (BetaREq.of_alpha (substTerm_alphaEq_of_not_free s x t hx))
  | .imp B C =>
      rw [substFormula.eq_def]
      simp only [freeVarOccurrencesFormula, List.mem_append, not_or] at hx
      exact FormulaBetaREq.imp
        (substFormula_betaREq_of_not_free B x t hx.1)
        (substFormula_betaREq_of_not_free C x t hx.2)
  | .all v B =>
      rw [substFormula.eq_def]
      by_cases hvx : v = x
      · simp only [hvx, beq_self_eq_true, ↓reduceIte]
        exact FormulaBetaREq.refl _
      · have hvxb : (v == x) = false := beq_eq_false_iff_ne.mpr hvx
        have hx_B : x ∉ freeVarOccurrencesFormula B := by
          intro hmem
          apply hx
          simp only [freeVarOccurrencesFormula, List.mem_filter, bne_iff_ne]
          exact ⟨hmem, Ne.symm hvx⟩
        simp only [hvxb, Bool.false_eq_true, ↓reduceIte]
        split
        · next hvt =>
          let freshId := Nat.max (maxVarIdFormula B) (Nat.max (maxVarIdTerm t) x.id) + 1
          let v' : Var := ⟨freshId, v.ty⟩
          have hle1 : maxVarIdFormula B ≤ Nat.max (maxVarIdFormula B) (Nat.max (maxVarIdTerm t) x.id) :=
            Nat.le_max_left _ _
          have hle2 : x.id ≤ Nat.max (maxVarIdFormula B) (Nat.max (maxVarIdTerm t) x.id) :=
            Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
          have hv'_not_all : v' ∉ allVarsFormula B := by
            apply not_mem_allVarsFormula_of_gt
            change maxVarIdFormula B < freshId
            omega
          have hv'_ne_x : x ≠ v' := by
            intro h; have := congrArg Var.id h; change x.id = freshId at this; omega
          have hx_ren : x ∉ freeVarOccurrencesFormula (renameFreeVarFormula B v v') := by
            intro hmem
            rcases mem_freeVarOccurrencesFormula_rename B v v' x hmem with h1 | h2
            · exact hx_B h1
            · exact hv'_ne_x h2
          have ih := substFormula_betaREq_of_not_free (renameFreeVarFormula B v v') x t hx_ren
          exact FormulaBetaREq.trans
            (FormulaBetaREq.all v' ih)
            (FormulaBetaREq.symm (FormulaBetaREq.all_rename v v' B rfl (.inr hv'_not_all)))
        · next hvt =>
          exact FormulaBetaREq.all v (substFormula_betaREq_of_not_free B x t hx_B)
termination_by formulaSize A
decreasing_by
  all_goals
    simp_wf
    simp [formulaSize, renameFreeVarFormula_size]
    try omega

theorem substTerm_var_self (r : Term) (x : Var) :
    substTerm r x (.var x) = r := by
  induction r with
  | var v =>
      rw [substTerm.eq_def]
      by_cases h : v = x
      · subst h; simp
      · have hb : (v == x) = false := beq_eq_false_iff_ne.mpr h
        simp [hb]
  | const c =>
      rw [substTerm.eq_def]
  | lam v body ih =>
      rw [substTerm.eq_def]
      by_cases h : v = x
      · subst h; simp
      · have hb : (v == x) = false := beq_eq_false_iff_ne.mpr h
        have hmem : v ∉ freeVarOccurrences (.var x) := by
          simp only [freeVarOccurrences, List.mem_singleton]
          exact h
        simp [hb, hmem, ih]
  | app t u iht ihu =>
      rw [substTerm.eq_def]
      simp [iht, ihu]

theorem substFormula_var_self (A : Formula) (x : Var) :
    substFormula A x (.var x) = A := by
  induction A with
  | bot | varX => rw [substFormula.eq_def]
  | atom s =>
      rw [substFormula.eq_def]
      simp [substTerm_var_self]
  | imp B C ihB ihC =>
      rw [substFormula.eq_def]
      simp [ihB, ihC]
  | all v B ih =>
      rw [substFormula.eq_def]
      by_cases h : v = x
      · subst h; simp
      · have hb : (v == x) = false := beq_eq_false_iff_ne.mpr h
        have hmem : v ∉ freeVarOccurrences (.var x) := by
          simp only [freeVarOccurrences, List.mem_singleton]
          exact h
        simp [hb, hmem, ih]

theorem HasType.renameFreeVar {r : Term} {ρ : Ty} (hr : HasType r ρ) (x y : Var)
    (hxy : x.ty = y.ty) : HasType (BBS2002.renameFreeVar r x y) ρ := by
  induction hr with
  | var v =>
      simp only [BBS2002.renameFreeVar]
      by_cases h : v = x
      · subst h; simp [hxy]; exact HasType.var y
      · have hb : (v == x) = false := beq_eq_false_iff_ne.mpr h
        simp [hb]; exact HasType.var v
  | const c => exact HasType.const c
  | lam v _ ih =>
      simp only [BBS2002.renameFreeVar]
      split
      · exact HasType.lam v (by assumption)
      · exact HasType.lam v ih
  | app _ _ iht ihs =>
      exact HasType.app iht ihs

@[simp] theorem substTerm_const (c : Const) (x : Var) (t : Term) :
    substTerm (.const c) x t = .const c := by
  rw [substTerm.eq_def]

@[simp] theorem substTerm_var_same (x : Var) (t : Term) :
    substTerm (.var x) x t = t := by
  rw [substTerm.eq_def]; simp

@[simp] theorem substFormula_bot (x : Var) (t : Term) :
    substFormula .bot x t = .bot := by
  rw [substFormula.eq_def]

@[simp] theorem substFormula_varX (x : Var) (t : Term) :
    substFormula .varX x t = .varX := by
  rw [substFormula.eq_def]

@[simp] theorem substFormula_atom (s : Term) (x : Var) (t : Term) :
    substFormula (.atom s) x t = .atom (substTerm s x t) := by
  rw [substFormula.eq_def]

@[simp] theorem substFormula_imp (B C : Formula) (x : Var) (t : Term) :
    substFormula (.imp B C) x t = .imp (substFormula B x t) (substFormula C x t) := by
  rw [substFormula.eq_def]

@[simp] theorem substFormula_neg (B : Formula) (x : Var) (t : Term) :
    substFormula (Formula.neg B) x t = Formula.neg (substFormula B x t) := by
  simp [Formula.neg]

@[simp] theorem substFormula_dneg (B : Formula) (x : Var) (t : Term) :
    substFormula (Formula.dneg B) x t = Formula.dneg (substFormula B x t) := by
  simp [Formula.dneg]

@[simp] theorem substFormula_falseAtom (x : Var) (t : Term) :
    substFormula Formula.falseAtom x t = Formula.falseAtom := by
  simp [Formula.falseAtom]

theorem HasType.substTerm {r : Term} {ρ : Ty} (hr : HasType r ρ) (x : Var) {s : Term}
    (hs : HasType s x.ty) : HasType (BBS2002.substTerm r x s) ρ := by
  match r with
  | .var v =>
      rw [BBS2002.substTerm.eq_def]
      cases hr
      by_cases h : v = x
      · subst h; simp [hs]
      · have hb : (v == x) = false := beq_eq_false_iff_ne.mpr h
        simp [hb]; exact HasType.var v
  | .const c =>
      rw [BBS2002.substTerm.eq_def]
      cases hr
      exact HasType.const c
  | .lam v body =>
      rw [BBS2002.substTerm.eq_def]
      cases hr with
      | lam _ hbody =>
          by_cases hvx : v = x
          · subst hvx
            simp only [beq_self_eq_true, ↓reduceIte]
            exact HasType.lam v hbody
          · have hvxb : (v == x) = false := beq_eq_false_iff_ne.mpr hvx
            simp only [hvxb, Bool.false_eq_true, ↓reduceIte]
            split
            · let freshId := Nat.max (maxVarIdTerm body) (Nat.max (maxVarIdTerm s) x.id) + 1
              let v' : Var := ⟨freshId, v.ty⟩
              have hren := HasType.renameFreeVar hbody v v' rfl
              exact HasType.lam v' (HasType.substTerm hren x hs)
            · exact HasType.lam v (HasType.substTerm hbody x hs)
  | .app t u =>
      rw [BBS2002.substTerm.eq_def]
      cases hr with
      | app ht hu =>
          exact HasType.app (HasType.substTerm ht x hs) (HasType.substTerm hu x hs)
termination_by rawSize r
decreasing_by
  all_goals
    simp_wf
    simp [rawSize, renameFreeVar_rawSize]
    try omega

theorem FormulaWellTyped.renameFreeVarFormula {A : Formula} (hA : FormulaWellTyped A)
    (x y : Var) (hxy : x.ty = y.ty) : FormulaWellTyped (BBS2002.renameFreeVarFormula A x y) := by
  induction hA with
  | bot => exact .bot
  | varX => exact .varX
  | atom ht => exact .atom (ht.renameFreeVar x y hxy)
  | imp _ _ ih1 ih2 => exact .imp ih1 ih2
  | all v hB ih =>
      simp only [BBS2002.renameFreeVarFormula]
      split
      · exact .all v hB
      · exact .all v ih

theorem FormulaWellTyped.substFormula {A : Formula} (hA : FormulaWellTyped A)
    (x : Var) {t : Term} (ht : HasType t x.ty) :
    FormulaWellTyped (BBS2002.substFormula A x t) := by
  match A with
  | .bot =>
      simp; exact .bot
  | .varX =>
      simp; exact .varX
  | .atom s =>
      simp
      cases hA with
      | atom hs => exact .atom (hs.substTerm x ht)
  | .imp B C =>
      simp
      cases hA with
      | imp hB hC => exact .imp (hB.substFormula x ht) (hC.substFormula x ht)
  | .all v B =>
      rw [BBS2002.substFormula.eq_def]
      cases hA with
      | all _ hB =>
          by_cases hvx : v = x
          · subst hvx
            simp only [beq_self_eq_true, ↓reduceIte]
            exact .all v hB
          · have hvxb : (v == x) = false := beq_eq_false_iff_ne.mpr hvx
            simp only [hvxb, Bool.false_eq_true, ↓reduceIte]
            split
            · let freshId := Nat.max (maxVarIdFormula B) (Nat.max (maxVarIdTerm t) x.id) + 1
              let v' : Var := ⟨freshId, v.ty⟩
              have hren := hB.renameFreeVarFormula v v' rfl
              exact .all v' (hren.substFormula x ht)
            · exact .all v (hB.substFormula x ht)
termination_by formulaSize A
decreasing_by
  all_goals
    simp_wf
    simp [formulaSize, renameFreeVarFormula_size]
    try omega

theorem isLFormula_renameFreeVarFormula (A : Formula) (x y : Var) :
    isLFormula (renameFreeVarFormula A x y) = isLFormula A := by
  induction A with
  | bot | varX | atom _ => rfl
  | imp B C ihB ihC => simp [renameFreeVarFormula, isLFormula, ihB, ihC]
  | all v B ih =>
      simp only [renameFreeVarFormula]
      split
      · rfl
      · simp [isLFormula, ih]

theorem isLFormula_substFormula (A : Formula) (x : Var) (t : Term) :
    isLFormula (substFormula A x t) = isLFormula A := by
  match A with
  | .bot | .varX | .atom _ =>
      simp [isLFormula]
  | .imp B C =>
      simp [isLFormula, isLFormula_substFormula B x t, isLFormula_substFormula C x t]
  | .all v B =>
      rw [substFormula.eq_def]
      by_cases hvx : v = x
      · subst hvx
        simp [isLFormula]
      · have hvxb : (v == x) = false := beq_eq_false_iff_ne.mpr hvx
        simp only [hvxb, Bool.false_eq_true, ↓reduceIte]
        split
        · let freshId := Nat.max (maxVarIdFormula B) (Nat.max (maxVarIdTerm t) x.id) + 1
          let v' : Var := ⟨freshId, v.ty⟩
          have ih1 := isLFormula_substFormula (renameFreeVarFormula B v v') x t
          have ih2 := isLFormula_renameFreeVarFormula B v v'
          exact ih1.trans ih2
        · exact isLFormula_substFormula B x t
termination_by formulaSize A
decreasing_by
  all_goals
    simp_wf
    simp [formulaSize, renameFreeVarFormula_size]
    try omega

theorem FormulaWellTyped.neg {A : Formula} (hA : FormulaWellTyped A) :
    FormulaWellTyped (Formula.neg A) :=
  .imp hA .bot

theorem FormulaWellTyped.dneg {A : Formula} (hA : FormulaWellTyped A) :
    FormulaWellTyped (Formula.dneg A) :=
  hA.neg.neg

theorem FormulaWellTyped.falseAtom : FormulaWellTyped Formula.falseAtom :=
  .atom (.const .falseConst)

theorem FormulaWellTyped.trueAtom : FormulaWellTyped (.atom (.const .trueConst)) :=
  .atom (.const .trueConst)

theorem FormulaWellTyped.substBotWithFalse {A : Formula} (hA : FormulaWellTyped A) :
    FormulaWellTyped (BBS2002.substBotWithFalse A) := by
  induction hA with
  | bot => exact .falseAtom
  | varX => exact .varX
  | atom ht => exact .atom ht
  | imp _ _ ih1 ih2 => exact .imp ih1 ih2
  | all x _ ih => exact .all x ih

@[simp]
theorem isLFormula_neg (A : Formula) : isLFormula (Formula.neg A) = isLFormula A := by
  simp [Formula.neg, isLFormula]

@[simp]
theorem isLFormula_dneg (A : Formula) : isLFormula (Formula.dneg A) = isLFormula A := by
  simp [Formula.dneg]

theorem SysConfig.allowsFormula.bot (sys : SysConfig) : sys.allowsFormula .bot :=
  ⟨.bot, .inr rfl⟩

theorem SysConfig.allowsFormula.falseAtom (sys : SysConfig) : sys.allowsFormula Formula.falseAtom :=
  ⟨FormulaWellTyped.falseAtom, .inr rfl⟩

theorem SysConfig.allowsFormula.trueAtom (sys : SysConfig) :
    sys.allowsFormula (.atom (.const .trueConst)) :=
  ⟨FormulaWellTyped.trueAtom, .inr rfl⟩

theorem SysConfig.allowsFormula.imp {sys : SysConfig} {A B : Formula}
    (hA : sys.allowsFormula A) (hB : sys.allowsFormula B) :
    sys.allowsFormula (.imp A B) := by
  refine ⟨.imp hA.1 hB.1, ?_⟩
  rcases hA.2 with hX | hLA
  · exact .inl hX
  · rcases hB.2 with hX | hLB
    · exact .inl hX
    · exact .inr (by simp [isLFormula, hLA, hLB])

theorem SysConfig.allowsFormula.neg {sys : SysConfig} {A : Formula}
    (hA : sys.allowsFormula A) : sys.allowsFormula (Formula.neg A) :=
  hA.imp (.bot sys)

theorem SysConfig.allowsFormula.dneg {sys : SysConfig} {A : Formula}
    (hA : sys.allowsFormula A) : sys.allowsFormula (Formula.dneg A) :=
  hA.neg.neg

theorem SysConfig.allowsFormula.all (x : Var) {sys : SysConfig} {A : Formula}
    (hA : sys.allowsFormula A) : sys.allowsFormula (.all x A) := by
  refine ⟨.all x hA.1, ?_⟩
  rcases hA.2 with hX | hLA
  · exact .inl hX
  · exact .inr (by simp [isLFormula, hLA])

theorem SysConfig.allowsFormula.substFormula {sys : SysConfig} {A : Formula}
    (hA : sys.allowsFormula A) (x : Var) {t : Term} (ht : HasType t x.ty) :
    sys.allowsFormula (BBS2002.substFormula A x t) := by
  refine ⟨hA.1.substFormula x ht, ?_⟩
  rcases hA.2 with hX | hL
  · exact .inl hX
  · exact .inr (by rw [isLFormula_substFormula]; exact hL)

theorem SysConfig.allowsFormula.impMany {sys : SysConfig} {Γ : List Formula} {B : Formula}
    (hΓ : ∀ D ∈ Γ, sys.allowsFormula D) (hB : sys.allowsFormula B) :
    sys.allowsFormula (Formula.impMany Γ B) := by
  induction Γ with
  | nil => exact hB
  | cons D Γ ih =>
      exact (hΓ D (List.Mem.head _)).imp (ih (fun E hE => hΓ E (List.Mem.tail _ hE)))

theorem Provable.mp {sys : SysConfig} {A B : Formula}
    (h1 : Provable sys (.imp A B)) (h2 : Provable sys A) :
    Provable sys B := by
  rcases h1 with ⟨M, hM, hMC⟩
  rcases h2 with ⟨N, hN, hNC⟩
  refine ⟨.appAssump M N, .appAssump hM hN, ?_⟩
  simp [freeAssumpVars, hMC, hNC]

theorem Provable.id {sys : SysConfig} {A : Formula} (hA : sys.allowsFormula A) :
    Provable sys (.imp A A) := by
  let u : AssumpVar := ⟨0, A⟩
  refine ⟨.lamAssump u (.assump u), .lamAssump u hA (.assump u hA), ?_⟩
  simp [freeAssumpVars]

theorem Provable.weaken {sys : SysConfig} {A B : Formula}
    (hA : sys.allowsFormula A) (hB : Provable sys B) :
    Provable sys (.imp A B) := by
  rcases hB with ⟨M, hM, hMC⟩
  let u : AssumpVar := ⟨0, A⟩
  refine ⟨.lamAssump u M, .lamAssump u hA hM, ?_⟩
  simp [freeAssumpVars, hMC]

theorem Provable.imp_const {sys : SysConfig} {A B : Formula}
    (hA : sys.allowsFormula A) (hB : sys.allowsFormula B) :
    Provable sys (.imp A (.imp B A)) := by
  let u0 : AssumpVar := ⟨0, A⟩
  let u1 : AssumpVar := ⟨1, B⟩
  refine ⟨.lamAssump u0 (.lamAssump u1 (.assump u0)),
    .lamAssump u0 hA (.lamAssump u1 hB (.assump u0 hA)), ?_⟩
  apply freeAssumpVars_eq_nil_of_forall_not_mem
  intro v hv
  rcases mem_freeAssumpVars_lamAssump.mp hv with ⟨hv, hne0⟩
  rcases mem_freeAssumpVars_lamAssump.mp hv with ⟨hv, _⟩
  simp only [freeAssumpVars, List.mem_singleton] at hv
  exact hne0 hv

theorem Provable.imp_distrib {sys : SysConfig} {A B C : Formula}
    (hA : sys.allowsFormula A) (hB : sys.allowsFormula B) (hC : sys.allowsFormula C) :
    Provable sys (.imp (.imp A (.imp B C)) (.imp (.imp A B) (.imp A C))) := by
  let u0 : AssumpVar := ⟨0, .imp A (.imp B C)⟩
  let u1 : AssumpVar := ⟨1, .imp A B⟩
  let u2 : AssumpVar := ⟨2, A⟩
  have hu0 : sys.allowsFormula u0.formula := hA.imp (hB.imp hC)
  have hu1 : sys.allowsFormula u1.formula := hA.imp hB
  have hu2 : sys.allowsFormula u2.formula := hA
  refine ⟨.lamAssump u0 (.lamAssump u1 (.lamAssump u2
      (.appAssump (.appAssump (.assump u0) (.assump u2)) (.appAssump (.assump u1) (.assump u2))))),
    .lamAssump u0 hu0 (.lamAssump u1 hu1 (.lamAssump u2 hu2
      (.appAssump (.appAssump (.assump u0 hu0) (.assump u2 hu2))
        (.appAssump (.assump u1 hu1) (.assump u2 hu2))))), ?_⟩
  apply freeAssumpVars_eq_nil_of_forall_not_mem
  intro v hv
  rcases mem_freeAssumpVars_lamAssump.mp hv with ⟨hv, hne0⟩
  rcases mem_freeAssumpVars_lamAssump.mp hv with ⟨hv, hne1⟩
  rcases mem_freeAssumpVars_lamAssump.mp hv with ⟨hv, hne2⟩
  rcases mem_freeAssumpVars_appAssump.mp hv with hv | hv
  · rcases mem_freeAssumpVars_appAssump.mp hv with hv | hv
    · simp only [freeAssumpVars, List.mem_singleton] at hv; exact hne0 hv
    · simp only [freeAssumpVars, List.mem_singleton] at hv; exact hne2 hv
  · rcases mem_freeAssumpVars_appAssump.mp hv with hv | hv
    · simp only [freeAssumpVars, List.mem_singleton] at hv; exact hne1 hv
    · simp only [freeAssumpVars, List.mem_singleton] at hv; exact hne2 hv

theorem Provable.imp_mp {sys : SysConfig} {D A B : Formula}
    (hD : sys.allowsFormula D) (hA : sys.allowsFormula A) (hB : sys.allowsFormula B)
    (h1 : Provable sys (.imp D (.imp A B))) (h2 : Provable sys (.imp D A)) :
    Provable sys (.imp D B) :=
  Provable.mp (Provable.mp (Provable.imp_distrib hD hA hB) h1) h2

theorem Provable.imp_trans {sys : SysConfig} {A B C : Formula}
    (hA : sys.allowsFormula A) (hB : sys.allowsFormula B) (hC : sys.allowsFormula C)
    (h1 : Provable sys (.imp A B)) (h2 : Provable sys (.imp B C)) :
    Provable sys (.imp A C) :=
  Provable.imp_mp hA hB hC (Provable.weaken hA h2) h1

theorem impMany_append (Γ₁ Γ₂ : List Formula) (B : Formula) :
    Formula.impMany (Γ₁ ++ Γ₂) B = Formula.impMany Γ₁ (Formula.impMany Γ₂ B) := by
  induction Γ₁ with
  | nil => rfl
  | cons D Γ₁ ih => simp [Formula.impMany, ih]

theorem Provable.ctx_const {sys : SysConfig} {Γ : List Formula} {A : Formula}
    (hΓ : ∀ D ∈ Γ, sys.allowsFormula D) (hA : Provable sys A) :
    Provable sys (Formula.impMany Γ A) := by
  induction Γ with
  | nil => exact hA
  | cons D Γ ih =>
      exact Provable.weaken (hΓ D (List.Mem.head _)) (ih (fun E hE => hΓ E (List.Mem.tail _ hE)))

theorem Provable.ctx_distrib {sys : SysConfig} {Γ : List Formula} {A B : Formula}
    (hΓ : ∀ D ∈ Γ, sys.allowsFormula D)
    (hA : sys.allowsFormula A) (hB : sys.allowsFormula B) :
    Provable sys (.imp (Formula.impMany Γ (.imp A B))
      (.imp (Formula.impMany Γ A) (Formula.impMany Γ B))) := by
  induction Γ with
  | nil => exact Provable.id (hA.imp hB)
  | cons D Γ ih =>
      have hD : sys.allowsFormula D := hΓ D (List.Mem.head _)
      have hΓ' : ∀ E ∈ Γ, sys.allowsFormula E := fun E hE => hΓ E (List.Mem.tail _ hE)
      have hX : sys.allowsFormula (Formula.impMany Γ (.imp A B)) := .impMany hΓ' (hA.imp hB)
      have hY : sys.allowsFormula (Formula.impMany Γ A) := .impMany hΓ' hA
      have hZ : sys.allowsFormula (Formula.impMany Γ B) := .impMany hΓ' hB
      have h1 : Provable sys (.imp (.imp D (Formula.impMany Γ (.imp A B)))
          (.imp D (.imp (Formula.impMany Γ A) (Formula.impMany Γ B)))) :=
        Provable.mp (Provable.imp_distrib hD hX (hY.imp hZ)) (Provable.weaken hD (ih hΓ'))
      have h2 : Provable sys (.imp (.imp D (.imp (Formula.impMany Γ A) (Formula.impMany Γ B)))
          (.imp (.imp D (Formula.impMany Γ A)) (.imp D (Formula.impMany Γ B)))) :=
        Provable.imp_distrib hD hY hZ
      exact Provable.imp_trans (hD.imp hX) (hD.imp (hY.imp hZ)) ((hD.imp hY).imp (hD.imp hZ)) h1 h2

theorem Provable.ctx_mp {sys : SysConfig} {Γ : List Formula} {A B : Formula}
    (hΓ : ∀ D ∈ Γ, sys.allowsFormula D)
    (hA : sys.allowsFormula A) (hB : sys.allowsFormula B)
    (h1 : Provable sys (Formula.impMany Γ (.imp A B)))
    (h2 : Provable sys (Formula.impMany Γ A)) :
    Provable sys (Formula.impMany Γ B) :=
  Provable.mp (Provable.mp (Provable.ctx_distrib hΓ hA hB) h1) h2

theorem Provable.imp_ctx_const {sys : SysConfig} {Γ : List Formula} {A : Formula}
    (hΓ : ∀ D ∈ Γ, sys.allowsFormula D) (hA : sys.allowsFormula A) :
    Provable sys (.imp A (Formula.impMany Γ A)) := by
  induction Γ with
  | nil => exact Provable.id hA
  | cons E Γ ih =>
      have hE : sys.allowsFormula E := hΓ E (List.Mem.head _)
      have hΓ' : ∀ F ∈ Γ, sys.allowsFormula F := fun F hF => hΓ F (List.Mem.tail _ hF)
      have hSub : Provable sys (.imp A (Formula.impMany Γ A)) := ih hΓ'
      have hK : Provable sys (.imp (Formula.impMany Γ A) (.imp E (Formula.impMany Γ A))) :=
        Provable.imp_const (.impMany hΓ' hA) hE
      exact Provable.imp_trans hA (.impMany hΓ' hA) (hE.imp (.impMany hΓ' hA)) hSub hK

theorem Provable.ctx_hyp {sys : SysConfig} {Γ : List Formula} {A : Formula}
    (hΓ : ∀ D ∈ Γ, sys.allowsFormula D) (hmem : A ∈ Γ) :
    Provable sys (Formula.impMany Γ A) := by
  induction Γ with
  | nil => cases hmem
  | cons D Γ ih =>
      have hD : sys.allowsFormula D := hΓ D (List.Mem.head _)
      have hΓ' : ∀ E ∈ Γ, sys.allowsFormula E := fun E hE => hΓ E (List.Mem.tail _ hE)
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Provable.imp_ctx_const hΓ' hD
      · exact Provable.weaken hD (ih hΓ' hmem)

theorem Provable.imp_congr {sys : SysConfig} {A A' B B' : Formula}
    (hA : sys.allowsFormula A) (hA' : sys.allowsFormula A')
    (hB : sys.allowsFormula B) (hB' : sys.allowsFormula B')
    (hAA' : Provable sys (.imp A' A)) (hBB' : Provable sys (.imp B B')) :
    Provable sys (.imp (.imp A B) (.imp A' B')) := by
  let Γ : List Formula := [.imp A B, A']
  have hΓ : ∀ D ∈ Γ, sys.allowsFormula D := by
    intro D hD
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl
    · exact hA.imp hB
    · exact hA'
  have h1 : Provable sys (Formula.impMany Γ (.imp A B)) :=
    Provable.ctx_hyp hΓ (by simp [Γ])
  have h2 : Provable sys (Formula.impMany Γ A') :=
    Provable.ctx_hyp hΓ (by simp [Γ])
  have h3 : Provable sys (Formula.impMany Γ A) :=
    Provable.ctx_mp hΓ hA' hA (Provable.ctx_const hΓ hAA') h2
  have h4 : Provable sys (Formula.impMany Γ B) :=
    Provable.ctx_mp hΓ hA hB h1 h3
  exact Provable.ctx_mp hΓ hB hB' (Provable.ctx_const hΓ hBB') h4

theorem Provable.all_intro {sys : SysConfig} (x : Var) {A : Formula}
    (h : Provable sys A) : Provable sys (.all x A) := by
  rcases h with ⟨M, hM, hMC⟩
  refine ⟨.lamTerm x M, .lamTerm x ?_ hM, ?_⟩
  · intro u hu
    rw [hMC] at hu
    cases hu
  · simp [freeAssumpVars, hMC]

theorem Provable.imp_all_intro {sys : SysConfig} (x : Var) {Γ A : Formula}
    (hΓ : sys.allowsFormula Γ) (hx : x ∉ freeVarsFormula Γ)
    (h : Provable sys (.imp Γ A)) :
    Provable sys (.imp Γ (.all x A)) := by
  rcases h with ⟨M, hM, hMC⟩
  let u : AssumpVar := ⟨0, Γ⟩
  refine ⟨.lamAssump u (.lamTerm x (.appAssump M (.assump u))),
    .lamAssump u hΓ (.lamTerm x ?_ (.appAssump hM (.assump u hΓ))), ?_⟩
  · intro v hv
    rcases mem_freeAssumpVars_appAssump.mp hv with hv | hv
    · rw [hMC] at hv; cases hv
    · simp only [freeAssumpVars, List.mem_singleton] at hv
      subst hv
      exact hx
  · apply freeAssumpVars_eq_nil_of_forall_not_mem
    intro v hv
    rcases mem_freeAssumpVars_lamAssump.mp hv with ⟨hv, hne⟩
    change v ∈ freeAssumpVars (.appAssump M (.assump u)) at hv
    rcases mem_freeAssumpVars_appAssump.mp hv with hv | hv
    · rw [hMC] at hv; cases hv
    · simp only [freeAssumpVars, List.mem_singleton] at hv
      exact hne hv

theorem Provable.imp_all_elim {sys : SysConfig} (x : Var) (t : Term) {A : Formula}
    (ht : HasType t x.ty) (hA : sys.allowsFormula A) :
    Provable sys (.imp (.all x A) (substFormula A x t)) := by
  let u : AssumpVar := ⟨0, .all x A⟩
  have hu : sys.allowsFormula u.formula := hA.all x
  refine ⟨.lamAssump u (.appTerm (.assump u) t),
    .lamAssump u hu (.appTerm t ht (.assump u hu)), ?_⟩
  simp [freeAssumpVars]

theorem Provable.imp_all_elim_self {sys : SysConfig} (x : Var) {A : Formula}
    (hA : sys.allowsFormula A) :
    Provable sys (.imp (.all x A) A) := by
  have h := Provable.imp_all_elim x (.var x) (HasType.var x) hA
  rwa [substFormula_var_self] at h

theorem Provable.all_elim {sys : SysConfig} (x : Var) (t : Term) {A : Formula}
    (ht : HasType t x.ty) (hA : sys.allowsFormula A)
    (h : Provable sys (.all x A)) :
    Provable sys (substFormula A x t) :=
  Provable.mp (Provable.imp_all_elim x t ht hA) h

theorem not_mem_freeVarsFormula_all (x : Var) (A : Formula) :
    x ∉ freeVarsFormula (.all x A) := by
  simp [freeVarsFormula]

theorem Provable.all_congr {sys : SysConfig} (x : Var) {A B : Formula}
    (hA : sys.allowsFormula A) (hB : sys.allowsFormula B)
    (hAB : Provable sys (.imp A B)) :
    Provable sys (.imp (.all x A) (.all x B)) := by
  have h1 : Provable sys (.imp (.all x A) A) := Provable.imp_all_elim_self x hA
  have h2 : Provable sys (.imp (.all x A) B) := Provable.imp_trans (hA.all x) hA hB h1 hAB
  exact Provable.imp_all_intro x (hA.all x) (not_mem_freeVarsFormula_all x A) h2

theorem Provable.conv {sys : SysConfig} {A B : Formula}
    (h : Provable sys A) (hB : sys.allowsFormula B) (heq : FormulaBetaREq A B) :
    Provable sys B := by
  rcases h with ⟨M, hM, hMC⟩
  exact ⟨M, .conv hM hB heq, hMC⟩


end BBS2002


/- Local checked proof module: MrBasics -/

namespace BBS2002.V2

theorem tau_eq_none_of_isL (ν : Ty) (A : Formula) (hA : isLFormula A = true) :
    tau ν A = none := by
  induction A with
  | bot | atom _ => rfl
  | varX => cases hA
  | imp A B ihA ihB =>
      simp only [isLFormula, Bool.and_eq_true] at hA
      simp only [tau, ihA hA.1, ihB hA.2]
  | all x A ih =>
      simp only [tau, ih hA]

theorem freshVar_not_mem_allVars_left {ν : Ty} (comp : CompTerm ν) (r : Option Term)
    (A B : Formula) (ρ : Ty) :
    freshVar comp r A B ρ ∉ allVarsFormula A := by
  apply not_mem_allVarsFormula_of_gt
  simp only [freshVar, freshMrVarId]
  exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))

theorem mrFormula_betaREq_of_isL (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (r : Realizer (tau ν A)) (hA : isLFormula A = true) :
    FormulaBetaREq (mrFormula ν comp A r) A := by
  match A with
  | .bot =>
      rw [mrFormula.eq_def ν comp .bot r]
      exact .bot
  | .varX => cases hA
  | .atom t =>
      rw [mrFormula.eq_def ν comp (.atom t) r]
      exact .refl _
  | .imp A B =>
      simp only [isLFormula, Bool.and_eq_true] at hA
      have htA := tau_eq_none_of_isL ν A hA.1
      have htB := tau_eq_none_of_isL ν B hA.2
      rw [mrFormula.eq_def ν comp (.imp A B) r]
      dsimp only
      split
      · exact .imp (mrFormula_betaREq_of_isL ν comp A _ hA.1)
          (mrFormula_betaREq_of_isL ν comp B _ hA.2)
      all_goals simp_all
  | .all x A =>
      have htA := tau_eq_none_of_isL ν A hA
      rw [mrFormula.eq_def ν comp (.all x A) r]
      dsimp only
      split
      · refine FormulaBetaREq.trans (.all _ ?_)
          (.symm (.all_rename x _ A rfl (.inr ?_)))
        · apply mrFormula_betaREq_of_isL
          simpa only [isLFormula_renameFreeVarFormula, isLFormula] using hA
        · intro hy
          apply freshVar_not_mem_allVars_left comp r.toOption (.all x A) .bot x.ty
          exact List.mem_cons_of_mem x hy
      · simp_all
termination_by formulaSize A
decreasing_by
  all_goals simp_wf
  all_goals try simp [formulaSize, renameFreeVarFormula_size]
  all_goals omega

theorem mrFormula_isL (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (r : Realizer (tau ν A)) : isLFormula (mrFormula ν comp A r) = true := by
  match A with
  | .varX =>
      rw [mrFormula.eq_def ν comp .varX r]
      exact (isLFormula_substFormula comp.body comp.var r).trans comp.body_isL
  | .bot =>
      rw [mrFormula.eq_def ν comp .bot r]
      rfl
  | .atom t =>
      rw [mrFormula.eq_def ν comp (.atom t) r]
      rfl
  | .imp A B =>
      rw [mrFormula.eq_def ν comp (.imp A B) r]
      dsimp only
      split
      all_goals
        exact Bool.and_eq_true_iff.mpr
          ⟨mrFormula_isL ν comp A _, mrFormula_isL ν comp B _⟩
  | .all x A =>
      rw [mrFormula.eq_def ν comp (.all x A) r]
      dsimp only
      split
      all_goals exact mrFormula_isL ν comp _ _
termination_by formulaSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [formulaSize, renameFreeVarFormula_size]
  all_goals omega

@[simp] theorem Realizer.typed_cast {τ σ : Option Ty} (h : τ = σ) (r : Realizer τ) :
    (Realizer.cast h r).Typed ↔ r.Typed := by
  cases h
  rfl

theorem mrFormula_wellTyped (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (r : Realizer (tau ν A)) (hA : FormulaWellTyped A) (hr : r.Typed) :
    FormulaWellTyped (mrFormula ν comp A r) := by
  match A with
  | .varX =>
      rw [mrFormula.eq_def ν comp .varX r]
      apply comp.body_wt.substFormula
      rw [comp.var_ty]
      exact hr
  | .bot =>
      rw [mrFormula.eq_def ν comp .bot r]
      exact .bot
  | .atom t =>
      rw [mrFormula.eq_def ν comp (.atom t) r]
      exact hA
  | .imp A B =>
      cases hA with
      | imp hA hB =>
          rw [mrFormula.eq_def ν comp (.imp A B) r]
          dsimp only
          split
          · exact .imp
              (mrFormula_wellTyped ν comp A _ hA
                ((Realizer.typed_cast (τ := none) _ ()).mpr True.intro))
              (mrFormula_wellTyped ν comp B _ hB
                ((Realizer.typed_cast (τ := none) _ ()).mpr True.intro))
          · exact .imp
              (mrFormula_wellTyped ν comp A _ hA
                ((Realizer.typed_cast (τ := none) _ ()).mpr True.intro))
              (mrFormula_wellTyped ν comp B _ hB ((Realizer.typed_cast _ r).mpr hr))
          · refine .all _ (.imp (mrFormula_wellTyped ν comp A _ hA ?_)
              (mrFormula_wellTyped ν comp B _ hB
                ((Realizer.typed_cast (τ := none) _ ()).mpr True.intro)))
            exact (Realizer.typed_cast _ _).mpr (.var _)
          · refine .all _ (.imp (mrFormula_wellTyped ν comp A _ hA ?_)
              (mrFormula_wellTyped ν comp B _ hB ?_))
            · exact (Realizer.typed_cast _ _).mpr (.var _)
            · exact (Realizer.typed_cast _ _).mpr
                (HasType.app ((Realizer.typed_cast (σ := some (.arr _ _)) _ r).mpr hr) (.var _))
  | .all x A =>
      cases hA with
      | all _ hA =>
          rw [mrFormula.eq_def ν comp (.all x A) r]
          dsimp only
          split
          · exact .all _ (mrFormula_wellTyped ν comp _ _
              (hA.renameFreeVarFormula x _ rfl)
              ((Realizer.typed_cast (τ := none) _ ()).mpr True.intro))
          · refine .all _ (mrFormula_wellTyped ν comp _ _
              (hA.renameFreeVarFormula x _ rfl) ?_)
            exact (Realizer.typed_cast _ _).mpr
              (HasType.app ((Realizer.typed_cast (σ := some (.arr _ _)) _ r).mpr hr) (.var _))
termination_by formulaSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [formulaSize, renameFreeVarFormula_size]
  all_goals omega

end BBS2002.V2


/- Local checked proof module: FormulaSupport -/

namespace BBS2002.V2.Support

theorem rename_term_support (t : Term) (x y z : Var)
    (h : z ∈ freeVarOccurrences (renameFreeVar t x y)) :
    (z ∈ freeVarOccurrences t ∧ z ≠ x) ∨ z = y := by
  induction t with
  | var v =>
      simp only [renameFreeVar] at h
      split at h
      · exact .inr (by simpa [freeVarOccurrences] using h)
      · simp_all [freeVarOccurrences]
  | const c => cases h
  | app t s iht ihs =>
      simp only [renameFreeVar, freeVarOccurrences, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases iht h with ⟨hz, hx⟩ | hy
        · exact .inl ⟨.inl hz, hx⟩
        · exact .inr hy
      · rcases ihs h with ⟨hz, hx⟩ | hy
        · exact .inl ⟨.inr hz, hx⟩
        · exact .inr hy
  | lam v t ih =>
      simp only [renameFreeVar] at h
      split at h
      · simp_all [freeVarOccurrences]
      · simp only [freeVarOccurrences, List.mem_filter, bne_iff_ne] at h ⊢
        rcases ih h.1 with ⟨hz, hx⟩ | hy
        · exact .inl ⟨⟨hz, h.2⟩, hx⟩
        · exact .inr hy

theorem rename_formula_support (A : Formula) (x y z : Var)
    (h : z ∈ freeVarsFormula (renameFreeVarFormula A x y)) :
    (z ∈ freeVarsFormula A ∧ z ≠ x) ∨ z = y := by
  induction A with
  | bot | varX => cases h
  | atom t =>
      simp only [renameFreeVarFormula, freeVarsFormula, freeVars, mem_eraseDups_iff] at h ⊢
      exact rename_term_support t x y z h
  | imp A B ihA ihB =>
      simp only [renameFreeVarFormula, freeVarsFormula, mem_eraseDups_iff, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases ihA h with ⟨hz, hx⟩ | hy
        · exact .inl ⟨.inl hz, hx⟩
        · exact .inr hy
      · rcases ihB h with ⟨hz, hx⟩ | hy
        · exact .inl ⟨.inr hz, hx⟩
        · exact .inr hy
  | all v A ih =>
      simp only [renameFreeVarFormula] at h
      split at h
      · simp_all [freeVarsFormula]
      · simp only [freeVarsFormula, List.mem_filter, bne_iff_ne] at h ⊢
        rcases ih h.1 with ⟨hz, hx⟩ | hy
        · exact .inl ⟨⟨hz, h.2⟩, hx⟩
        · exact .inr hy

theorem subst_term_support (t : Term) (x : Var) (s : Term) (z : Var)
    (h : z ∈ freeVarOccurrences (substTerm t x s)) :
    (z ∈ freeVarOccurrences t ∧ z ≠ x) ∨ z ∈ freeVarOccurrences s := by
  match t with
  | .var v =>
      rw [substTerm.eq_def] at h
      dsimp only at h
      split at h
      · exact .inr h
      · simp_all [freeVarOccurrences]
  | .const c => simp [substTerm, freeVarOccurrences] at h
  | .app t u =>
      rw [substTerm.eq_def] at h
      dsimp only at h
      simp only [freeVarOccurrences, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases subst_term_support t x s z h with ⟨hz, hx⟩ | hs
        · exact .inl ⟨.inl hz, hx⟩
        · exact .inr hs
      · rcases subst_term_support u x s z h with ⟨hz, hx⟩ | hs
        · exact .inl ⟨.inr hz, hx⟩
        · exact .inr hs
  | .lam v t =>
      rw [substTerm.eq_def] at h
      dsimp only at h
      split at h
      · simp_all [freeVarOccurrences]
      · split at h
        · simp only [freeVarOccurrences, List.mem_filter, bne_iff_ne] at h
          rcases subst_term_support (renameFreeVar t v _) x s z h.1 with ⟨hz, hx⟩ | hs
          · rcases rename_term_support t v _ z hz with ⟨hz, hv⟩ | hy
            · exact .inl ⟨List.mem_filter.mpr ⟨hz, by simpa using hv⟩, hx⟩
            · exact False.elim (h.2 hy)
          · exact .inr hs
        · simp only [freeVarOccurrences, List.mem_filter, bne_iff_ne] at h
          rcases subst_term_support t x s z h.1 with ⟨hz, hx⟩ | hs
          · exact .inl ⟨List.mem_filter.mpr ⟨hz, by simpa using h.2⟩, hx⟩
          · exact .inr hs
termination_by rawSize t
decreasing_by
  all_goals simp_wf
  all_goals simp [rawSize, renameFreeVar_rawSize]
  all_goals omega

theorem subst_formula_support (A : Formula) (x : Var) (s : Term) (z : Var)
    (h : z ∈ freeVarsFormula (substFormula A x s)) :
    (z ∈ freeVarsFormula A ∧ z ≠ x) ∨ z ∈ freeVars s := by
  match A with
  | .bot | .varX => simp [substFormula, freeVarsFormula] at h
  | .atom t =>
      simp only [substFormula, freeVarsFormula, freeVars, mem_eraseDups_iff] at h ⊢
      exact subst_term_support t x s z h
  | .imp A B =>
      rw [substFormula.eq_def] at h
      dsimp only at h
      simp only [freeVarsFormula, mem_eraseDups_iff, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases subst_formula_support A x s z h with ⟨hz, hx⟩ | hs
        · exact .inl ⟨.inl hz, hx⟩
        · exact .inr hs
      · rcases subst_formula_support B x s z h with ⟨hz, hx⟩ | hs
        · exact .inl ⟨.inr hz, hx⟩
        · exact .inr hs
  | .all v A =>
      rw [substFormula.eq_def] at h
      dsimp only at h
      split at h
      · simp_all [freeVarsFormula]
      · split at h
        · simp only [freeVarsFormula, List.mem_filter, bne_iff_ne] at h
          rcases subst_formula_support (renameFreeVarFormula A v _) x s z h.1 with ⟨hz, hx⟩ | hs
          · rcases rename_formula_support A v _ z hz with ⟨hz, hv⟩ | hy
            · exact .inl ⟨List.mem_filter.mpr ⟨hz, by simpa using hv⟩, hx⟩
            · exact False.elim (h.2 hy)
          · exact .inr hs
        · simp only [freeVarsFormula, List.mem_filter, bne_iff_ne] at h
          rcases subst_formula_support A x s z h.1 with ⟨hz, hx⟩ | hs
          · exact .inl ⟨List.mem_filter.mpr ⟨hz, by simpa using h.2⟩, hx⟩
          · exact .inr hs
termination_by formulaSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [formulaSize, renameFreeVarFormula_size]
  all_goals omega

end BBS2002.V2.Support


/- Local checked proof module: Conversion -/

namespace BBS2002.V2.Conversion

/-- Substitution is application of an abstraction, modulo beta conversion. -/
theorem subst_term_congr {a b r s : Term} (x : Var)
    (hab : BetaREq a b) (hrs : BetaREq r s) :
    BetaREq (substTerm a x r) (substTerm b x s) :=
  .trans (.symm (.of_conv (.beta x a r)))
    (.trans (.app (.lam x hab) hrs) (.of_conv (.beta x b s)))

/-- A substitution outside a comprehension affects only its supplied argument. -/
theorem subst_term_comprehension (a : Term) (c x : Var) (r t : Term)
    (hx : x = c ∨ x ∉ freeVarOccurrences a) :
    BetaREq (substTerm (substTerm a c r) x t)
      (substTerm a c (substTerm r x t)) := by
  have hfree : x ∉ freeVarOccurrences (.lam c a) := by
    simp only [freeVarOccurrences, List.mem_filter, bne_iff_ne]
    rintro ⟨hxa, hxc⟩
    rcases hx with h | h
    · exact hxc h
    · exact h hxa
  refine .trans (subst_term_congr x (.symm (.of_conv (.beta c a r))) (.refl t)) ?_
  rw [substTerm.eq_def (.app (.lam c a) r) x t]
  exact .trans (.app (.of_alpha (substTerm_alphaEq_of_not_free (.lam c a) x t hfree))
    (.refl _)) (.of_conv (.beta c a (substTerm r x t)))

theorem subst_term_compose (a : Term) (c x : Var) (r t : Term)
    (hcx : c ≠ x) (hct : c ∉ freeVarOccurrences t) :
    BetaREq (substTerm (substTerm a c r) x t)
      (substTerm (substTerm a x t) c (substTerm r x t)) := by
  refine .trans (subst_term_congr x (.symm (.of_conv (.beta c a r))) (.refl t)) ?_
  rw [substTerm.eq_def (.app (.lam c a) r) x t]
  dsimp only
  rw [substTerm.eq_def (.lam c a) x t]
  simp only [beq_eq_false_iff_ne.mpr hcx, Bool.false_eq_true, if_false, hct]
  exact .of_conv (.beta c (substTerm a x t) (substTerm r x t))

theorem subst_term_commute_var (a : Term) (v z x : Var) (t : Term)
    (hvx : v ≠ x) (hzx : z ≠ x) (hvt : v ∉ freeVarOccurrences t) :
    BetaREq (substTerm (substTerm a v (.var z)) x t)
      (substTerm (substTerm a x t) v (.var z)) := by
  have h := subst_term_compose a v x (.var z) t hvx hvt
  have hz : substTerm (.var z) x t = .var z := by
    simp [substTerm, hzx]
  simpa only [hz] using h

theorem subst_term_fresh_var (a : Term) (x y : Var)
    (hy : y ∉ allVarsTerm a) :
    substTerm a x (.var y) = renameFreeVar a x y := by
  induction a with
  | var v => simp [substTerm, renameFreeVar]
  | const c => simp [renameFreeVar]
  | app a b iha ihb =>
      simp only [allVarsTerm, List.mem_append, not_or] at hy
      simp only [substTerm, renameFreeVar, iha hy.1, ihb hy.2]
  | lam v a ih =>
      simp only [allVarsTerm, List.mem_cons, not_or] at hy
      rw [substTerm.eq_def (.lam v a) x (.var y)]
      dsimp only
      simp only [renameFreeVar]
      split
      · rfl
      · have h : v ∉ freeVarOccurrences (.var y) := by
          simpa [freeVarOccurrences] using Ne.symm hy.1
        simp only [h, if_false, ih hy.2]

theorem subst_formula_fresh_var (A : Formula) (x y : Var)
    (hy : y ∉ allVarsFormula A) :
    substFormula A x (.var y) = renameFreeVarFormula A x y := by
  induction A with
  | bot | varX => simp [renameFreeVarFormula]
  | atom a =>
      simp only [allVarsFormula] at hy
      simp only [substFormula, renameFreeVarFormula, subst_term_fresh_var a x y hy]
  | imp A B ihA ihB =>
      simp only [allVarsFormula, List.mem_append, not_or] at hy
      simp only [substFormula, renameFreeVarFormula, ihA hy.1, ihB hy.2]
  | all v A ih =>
      simp only [allVarsFormula, List.mem_cons, not_or] at hy
      rw [substFormula.eq_def (.all v A) x (.var y)]
      dsimp only
      simp only [renameFreeVarFormula]
      split
      · rfl
      · have h : v ∉ freeVarOccurrences (.var y) := by
          simpa [freeVarOccurrences] using Ne.symm hy.1
        simp only [h, if_false, ih hy.2]

theorem formulaSize_subst (A : Formula) (x : Var) (t : Term) :
    formulaSize (substFormula A x t) = formulaSize A := by
  match A with
  | .bot | .varX | .atom _ => simp [formulaSize]
  | .imp A B => simp only [substFormula, formulaSize,
      formulaSize_subst A x t, formulaSize_subst B x t]
  | .all v A =>
      rw [substFormula.eq_def (.all v A) x t]
      dsimp only
      split
      · rfl
      · split
        · let v' : Var := ⟨Nat.max (maxVarIdFormula A) (Nat.max (maxVarIdTerm t) x.id) + 1, v.ty⟩
          have ih := formulaSize_subst (renameFreeVarFormula A v v') x t
          dsimp only [v'] at ih
          simp only [formulaSize, ih, renameFreeVarFormula_size]
        · simp only [formulaSize, formulaSize_subst A x t]
termination_by formulaSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [formulaSize, renameFreeVarFormula_size]
  all_goals omega

theorem formulaSize_betaREq {A B : Formula} (h : FormulaBetaREq A B) :
    formulaSize A = formulaSize B := by
  induction h with
  | bot | varX | atom | refl => rfl
  | imp _ _ ihA ihB => simp only [formulaSize, ihA, ihB]
  | all _ _ ih => simp only [formulaSize, ih]
  | all_rename => simp only [formulaSize, renameFreeVarFormula_size]
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end BBS2002.V2.Conversion


/- Local checked proof module: FormulaAlignment -/

namespace BBS2002.V2

theorem all_betaREq_of_fresh_subst (A B : Formula) (x y z : Var)
    (hx : x.ty = z.ty) (hy : y.ty = z.ty)
    (hzA : z ∉ allVarsFormula A) (hzB : z ∉ allVarsFormula B)
    (h : FormulaBetaREq (substFormula A x (.var z)) (substFormula B y (.var z))) :
    FormulaBetaREq (.all x A) (.all y B) := by
  rw [Conversion.subst_formula_fresh_var A x z hzA,
    Conversion.subst_formula_fresh_var B y z hzB] at h
  exact .trans (.all_rename x z A hx (.inr hzA))
    (.trans (.all z h) (.symm (.all_rename y z B hy (.inr hzB))))

end BBS2002.V2


/- Local checked proof module: MrTransport -/

namespace BBS2002.V2

theorem tau_substFormula (ν : Ty) (A : Formula) (x : Var) (t : Term) :
    tau ν (substFormula A x t) = tau ν A := by
  match A with
  | .bot | .varX | .atom _ => simp [tau]
  | .imp A B =>
      simp only [substFormula_imp, tau, tau_substFormula ν A x t, tau_substFormula ν B x t]
  | .all y A =>
      rw [substFormula.eq_def]
      dsimp only
      split
      · rfl
      · split
        · let y' : Var :=
            ⟨Nat.max (maxVarIdFormula A) (Nat.max (maxVarIdTerm t) x.id) + 1, y.ty⟩
          have ih := tau_substFormula ν (renameFreeVarFormula A y y') x t
          dsimp only [y'] at ih
          simp only [tau, ih, tau_renameFreeVarFormula]
        · simp only [tau, tau_substFormula ν A x t]
termination_by formulaSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [formulaSize, renameFreeVarFormula_size]
  all_goals omega

namespace Realizer

def subst {τ : Option Ty} (r : Realizer τ) (x : Var) (t : Term) : Realizer τ :=
  match τ with
  | none => ()
  | some _ => substTerm r x t

theorem subst_toOption {τ : Option Ty} (r : Realizer τ) (x : Var) (t : Term) :
    (subst r x t).toOption = r.toOption.map (fun q ↦ substTerm q x t) := by
  cases τ <;> rfl

theorem typed_subst {τ : Option Ty} (r : Realizer τ) (x : Var) (t : Term)
    (hr : r.Typed) (ht : HasType t x.ty) : (subst r x t).Typed := by
  cases τ with
  | none => trivial
  | some ρ => exact hr.substTerm x ht

end Realizer

namespace Realizer

def SupportedBy {τ : Option Ty} (r : Realizer τ) (P : Var → Prop) : Prop :=
  ∀ t ∈ r.toOption, ∀ z ∈ freeVars t, P z

theorem SupportedBy.cast {τ σ : Option Ty} {r : Realizer τ} {P : Var → Prop}
    (hr : r.SupportedBy P) (h : τ = σ) : (Realizer.cast h r).SupportedBy P := by
  cases h
  exact hr

theorem SupportedBy.mono {τ : Option Ty} {r : Realizer τ} {P Q : Var → Prop}
    (hr : r.SupportedBy P) (hPQ : ∀ z, P z → Q z) : r.SupportedBy Q :=
  fun t ht z hz ↦ hPQ z (hr t ht z hz)

theorem supportedBy_none (P : Var → Prop) : SupportedBy (τ := none) () P := by
  intro t ht
  exact False.elim (Option.not_mem_none t ht)

theorem supportedBy_some (ρ : Ty) (t : Term) (P : Var → Prop) :
    SupportedBy (τ := some ρ) t P ↔ ∀ z ∈ freeVars t, P z := by
  constructor
  · intro h
    exact h t rfl
  · intro h q hq
    simp only [toOption, Option.mem_def, Option.some.injEq] at hq
    subst q
    exact h

theorem supportedBy_var (x : Var) (P : Var → Prop) (hx : P x) :
    SupportedBy (τ := some x.ty) (.var x) P := by
  apply (supportedBy_some x.ty (.var x) P).mpr
  intro z hz
  have hzx : z = x := by simpa [freeVars, freeVarOccurrences] using hz
  exact hzx ▸ hx

theorem SupportedBy.app_var {ρ σ : Ty} {r : Realizer (some (.arr ρ σ))}
    {P : Var → Prop} (hr : r.SupportedBy P) (x : Var) (hx : P x) :
    SupportedBy (τ := some σ) (.app r (.var x)) P := by
  apply (supportedBy_some σ _ P).mpr
  intro z hz
  simp only [freeVars, mem_eraseDups_iff, freeVarOccurrences, List.mem_append,
    List.mem_singleton] at hz
  rcases hz with hz | rfl
  · exact (supportedBy_some (.arr ρ σ) r P).mp hr z
      (mem_eraseDups_of_mem' _ hz)
  · exact hx

end Realizer

theorem mrFormula_supportedBy (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (r : Realizer (tau ν A)) (P : Var → Prop)
    (hA : ∀ z ∈ freeVarsFormula A, P z) (hr : r.SupportedBy P)
    (hC : ∀ z ∈ freeVarsFormula comp.body, z ≠ comp.var → P z) :
    ∀ z ∈ freeVarsFormula (mrFormula ν comp A r), P z := by
  match A with
  | .varX =>
      rw [mrFormula.eq_def ν comp .varX r]
      intro z hz
      rcases Support.subst_formula_support comp.body comp.var r z hz with ⟨hz, hc⟩ | hz
      · exact hC z hz hc
      · exact (Realizer.supportedBy_some ν r P).mp hr z hz
  | .bot =>
      rw [mrFormula.eq_def ν comp .bot r]
      exact hA
  | .atom t =>
      rw [mrFormula.eq_def ν comp (.atom t) r]
      exact hA
  | .imp A B =>
      have hFA : ∀ z ∈ freeVarsFormula A, P z := by
        intro z hz
        apply hA z
        simp only [freeVarsFormula, mem_eraseDups_iff, List.mem_append]
        exact .inl hz
      have hFB : ∀ z ∈ freeVarsFormula B, P z := by
        intro z hz
        apply hA z
        simp only [freeVarsFormula, mem_eraseDups_iff, List.mem_append]
        exact .inr hz
      rw [mrFormula.eq_def ν comp (.imp A B) r]
      dsimp only
      split
      · intro z hz
        simp only [freeVarsFormula, mem_eraseDups_iff, List.mem_append] at hz
        rcases hz with hz | hz
        · exact mrFormula_supportedBy ν comp A _ P hFA
            ((Realizer.supportedBy_none P).cast _) hC z hz
        · exact mrFormula_supportedBy ν comp B _ P hFB
            ((Realizer.supportedBy_none P).cast _) hC z hz
      · intro z hz
        simp only [freeVarsFormula, mem_eraseDups_iff, List.mem_append] at hz
        rcases hz with hz | hz
        · exact mrFormula_supportedBy ν comp A _ P hFA
            ((Realizer.supportedBy_none P).cast _) hC z hz
        · exact mrFormula_supportedBy ν comp B _ P hFB (hr.cast _) hC z hz
      · next ρ hτA hτB =>
          let y := freshVar comp none A B ρ
          let Q := fun z ↦ P z ∨ z = y
          have hCA : ∀ z ∈ freeVarsFormula comp.body, z ≠ comp.var → Q z :=
            fun z hz hc ↦ .inl (hC z hz hc)
          intro z hz
          simp only [freeVarsFormula, List.mem_filter, bne_iff_ne,
            mem_eraseDups_iff, List.mem_append] at hz
          have hQ : Q z := by
            rcases hz.1 with hz | hz
            · exact mrFormula_supportedBy ν comp A _ Q
                (fun z hz ↦ .inl (hFA z hz))
                ((Realizer.supportedBy_var y Q (.inr rfl)).cast _) hCA z hz
            · exact mrFormula_supportedBy ν comp B _ Q
                (fun z hz ↦ .inl (hFB z hz))
                ((Realizer.supportedBy_none Q).cast _) hCA z hz
          exact hQ.resolve_right hz.2
      · next ρ σ hτA hτB =>
          let q : Realizer (some (.arr ρ σ)) :=
            Realizer.cast (by simp only [tau, hτA, hτB]) r
          let y := freshVar comp (some q) A B ρ
          let Q := fun z ↦ P z ∨ z = y
          have hCA : ∀ z ∈ freeVarsFormula comp.body, z ≠ comp.var → Q z :=
            fun z hz hc ↦ .inl (hC z hz hc)
          have hq : q.SupportedBy Q := (hr.cast _).mono (fun z hz ↦ .inl hz)
          intro z hz
          simp only [freeVarsFormula, List.mem_filter, bne_iff_ne,
            mem_eraseDups_iff, List.mem_append] at hz
          have hQ : Q z := by
            rcases hz.1 with hz | hz
            · exact mrFormula_supportedBy ν comp A _ Q
                (fun z hz ↦ .inl (hFA z hz))
                ((Realizer.supportedBy_var y Q (.inr rfl)).cast _) hCA z hz
            · exact mrFormula_supportedBy ν comp B _ Q
                (fun z hz ↦ .inl (hFB z hz))
                ((hq.app_var y (.inr rfl)).cast _) hCA z hz
          exact hQ.resolve_right hz.2
  | .all x A =>
      let y := freshVar comp r.toOption (.all x A) .bot x.ty
      let Q := fun z ↦ P z ∨ z = y
      have hFA : ∀ z ∈ freeVarsFormula (renameFreeVarFormula A x y), Q z := by
        intro z hz
        rcases Support.rename_formula_support A x y z hz with ⟨hz, hx⟩ | hy
        · apply Or.inl
          exact hA z (List.mem_filter.mpr ⟨hz, by simpa using hx⟩)
        · exact .inr hy
      have hCA : ∀ z ∈ freeVarsFormula comp.body, z ≠ comp.var → Q z :=
        fun z hz hc ↦ .inl (hC z hz hc)
      rw [mrFormula.eq_def ν comp (.all x A) r]
      dsimp only
      split
      · intro z hz
        simp only [freeVarsFormula, List.mem_filter, bne_iff_ne] at hz
        have hQ := mrFormula_supportedBy ν comp _ _ Q hFA
          ((Realizer.supportedBy_none Q).cast _) hCA z hz.1
        exact hQ.resolve_right hz.2
      · next ρ hτA =>
          let q : Realizer (some (.arr x.ty ρ)) :=
            Realizer.cast (by simp only [tau, hτA]) r
          have hq : q.SupportedBy Q := (hr.cast _).mono (fun z hz ↦ .inl hz)
          intro z hz
          simp only [freeVarsFormula, List.mem_filter, bne_iff_ne] at hz
          have hQ := mrFormula_supportedBy ν comp _ _ Q hFA
            ((hq.app_var y (.inr rfl)).cast _) hCA z hz.1
          exact hQ.resolve_right hz.2
termination_by formulaSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [formulaSize, renameFreeVarFormula_size]
  all_goals omega

theorem mrFormula_freeVars (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (r : Realizer (tau ν A)) (z : Var)
    (hz : z ∈ freeVarsFormula (mrFormula ν comp A r)) :
    z ∈ freeVarsFormula A ∨
      (∃ t ∈ r.toOption, z ∈ freeVars t) ∨
      (z ∈ freeVarsFormula comp.body ∧ z ≠ comp.var) := by
  apply mrFormula_supportedBy ν comp A r
    (fun z ↦ z ∈ freeVarsFormula A ∨
      (∃ t ∈ r.toOption, z ∈ freeVars t) ∨
      (z ∈ freeVarsFormula comp.body ∧ z ≠ comp.var))
    (fun z hz ↦ .inl hz)
    (fun t ht z hz ↦ .inr (.inl ⟨t, ht, hz⟩))
    (fun z hz hc ↦ .inr (.inr ⟨hz, hc⟩)) z hz

theorem mrFormula_not_free (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (r : Realizer (tau ν A)) (x : Var)
    (hA : x ∉ freeVarsFormula A) (hr : ∀ t ∈ r.toOption, x ∉ freeVars t)
    (hC : x = comp.var ∨ x ∉ freeVarsFormula comp.body) :
    x ∉ freeVarsFormula (mrFormula ν comp A r) := by
  intro hx
  rcases mrFormula_freeVars ν comp A r x hx with hx | ⟨t, ht, hx⟩ | ⟨hx, hc⟩
  · exact hA hx
  · exact hr t ht hx
  · rcases hC with hC | hC
    · exact hc hC
    · exact hC hx

namespace Realizer

def apply {τA τB : Option Ty} :
    Realizer (match τA, τB with
      | none, τB => τB
      | some _, none => none
      | some ρ, some σ => some (.arr ρ σ)) →
    Realizer τA → Realizer τB :=
  match τA, τB with
  | none, none => fun _ _ ↦ ()
  | none, some _ => fun r _ ↦ r
  | some _, none => fun _ _ ↦ ()
  | some _, some _ => fun r a ↦ Term.app r a

theorem apply_typed {τA τB : Option Ty}
    (r : Realizer (match τA, τB with
      | none, τB => τB
      | some _, none => none
      | some ρ, some σ => some (.arr ρ σ)))
    (a : Realizer τA) (hr : r.Typed) (ha : a.Typed) : (apply r a).Typed := by
  cases τA <;> cases τB
  · trivial
  · exact hr
  · trivial
  · exact HasType.app hr ha

def applyImp (ν : Ty) (A B : Formula) (r : Realizer (tau ν (.imp A B)))
    (a : Realizer (tau ν A)) : Realizer (tau ν B) :=
  apply (τA := tau ν A) (τB := tau ν B) r a

theorem applyImp_typed (ν : Ty) (A B : Formula)
    (r : Realizer (tau ν (.imp A B))) (a : Realizer (tau ν A))
    (hr : r.Typed) (ha : a.Typed) : (applyImp ν A B r a).Typed :=
  apply_typed r a hr ha

end Realizer


theorem tau_formulaBetaREq (ν : Ty) {A B : Formula} (h : FormulaBetaREq A B) :
    tau ν A = tau ν B := by
  induction h with
  | refl _ | bot | varX | atom _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | imp _ _ ih₁ ih₂ => simp only [tau, ih₁, ih₂]
  | all x _ ih => simp only [tau, ih]
  | all_rename x y A hxy _ =>
      simp only [tau, tau_renameFreeVarFormula, hxy]

theorem formulaSize_formulaBetaREq {A B : Formula} (h : FormulaBetaREq A B) :
    formulaSize A = formulaSize B := by
  induction h with
  | refl _ | bot | varX | atom _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | imp _ _ ih₁ ih₂ => simp only [formulaSize, ih₁, ih₂]
  | all x _ ih => simp only [formulaSize, ih]
  | all_rename x y A _ _ => simp only [formulaSize, renameFreeVarFormula_size]

namespace Realizer

theorem apply_toOption {τA τB : Option Ty}
    (r : Realizer (match τA, τB with
      | none, τB => τB
      | some _, none => none
      | some ρ, some σ => some (.arr ρ σ))) (a : Realizer τA) :
    (apply r a).toOption =
      match r.toOption, a.toOption with
      | none, _ => none
      | some f, none => some f
      | some f, some t => some (.app f t) := by
  cases τA <;> cases τB <;> rfl

theorem applyImp_toOption (ν : Ty) (A B : Formula)
    (r : Realizer (tau ν (.imp A B))) (a : Realizer (tau ν A)) :
    (applyImp ν A B r a).toOption =
      match r.toOption, a.toOption with
      | none, _ => none
      | some f, none => some f
      | some f, some t => some (.app f t) :=
  apply_toOption r a

def appTerm {ρ : Ty} {τ : Option Ty} :
    Realizer (match τ with | none => none | some σ => some (.arr ρ σ)) →
    Term → Realizer τ :=
  match τ with
  | none => fun _ _ ↦ ()
  | some _ => fun r t ↦ Term.app r t

theorem appTerm_typed {ρ : Ty} {τ : Option Ty}
    (r : Realizer (match τ with | none => none | some σ => some (.arr ρ σ)))
    (t : Term) (hr : r.Typed) (ht : HasType t ρ) : (appTerm r t).Typed := by
  cases τ
  · trivial
  · exact HasType.app hr ht

theorem appTerm_toOption {ρ : Ty} {τ : Option Ty}
    (r : Realizer (match τ with | none => none | some σ => some (.arr ρ σ))) (t : Term) :
    (appTerm r t).toOption = r.toOption.map (fun f ↦ Term.app f t) := by
  cases τ <;> rfl

def applyAll (ν : Ty) (x : Var) (A : Formula)
    (r : Realizer (tau ν (.all x A))) (t : Term) :
    Realizer (tau ν (substFormula A x t)) :=
  Realizer.cast (tau_substFormula ν A x t).symm
    (appTerm (ρ := x.ty) (τ := tau ν A) r t)

theorem applyAll_typed (ν : Ty) (x : Var) (A : Formula)
    (r : Realizer (tau ν (.all x A))) (t : Term)
    (hr : r.Typed) (ht : HasType t x.ty) : (applyAll ν x A r t).Typed :=
  (Realizer.typed_cast _ _).mpr (appTerm_typed r t hr ht)

theorem applyAll_toOption (ν : Ty) (x : Var) (A : Formula)
    (r : Realizer (tau ν (.all x A))) (t : Term) :
    (applyAll ν x A r t).toOption = r.toOption.map (fun f ↦ Term.app f t) :=
  (Realizer.toOption_cast _ _).trans (appTerm_toOption r t)

end Realizer

theorem formulaSize_substFormula (A : Formula) (x : Var) (t : Term) :
    formulaSize (substFormula A x t) = formulaSize A := by
  match A with
  | .bot | .varX | .atom _ => simp [formulaSize]
  | .imp A B =>
      simp only [substFormula_imp, formulaSize,
        formulaSize_substFormula A x t, formulaSize_substFormula B x t]
  | .all y A =>
      rw [substFormula.eq_def]
      dsimp only
      split
      · rfl
      · split
        · let y' : Var :=
            ⟨Nat.max (maxVarIdFormula A) (Nat.max (maxVarIdTerm t) x.id) + 1, y.ty⟩
          have ih := formulaSize_substFormula (renameFreeVarFormula A y y') x t
          dsimp only [y'] at ih
          simp only [formulaSize, ih, renameFreeVarFormula_size]
        · simp only [formulaSize, formulaSize_substFormula A x t]
termination_by formulaSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [formulaSize, renameFreeVarFormula_size]
  all_goals omega

namespace Realizer

theorem toOption_rel_refl {τ : Option Ty} (r : Realizer τ) :
    Option.Rel BetaREq r.toOption r.toOption := by
  cases τ
  · exact .none
  · exact .some (.refl _)

theorem toOption_rel_subst {τ σ : Option Ty} (r : Realizer τ) (s : Realizer σ)
    (x : Var) (t u : Term) (hrs : Option.Rel BetaREq r.toOption s.toOption)
    (htu : BetaREq t u) :
    Option.Rel BetaREq (subst r x t).toOption (subst s x u).toOption := by
  cases τ <;> cases σ
  · exact .none
  · cases hrs
  · cases hrs
  · cases hrs with
    | some hrs => exact .some (Conversion.subst_term_congr x hrs htu)

end Realizer

end BBS2002.V2


/- Local checked proof module: FormulaView -/

namespace BBS2002.V2.FormulaView

inductive View where
  | bot
  | varX
  | atom : Term → View
  | imp : View → View → View
  | all : Ty → View → View

def mapTerms (f : Term → Term) : View → View
  | .bot => .bot
  | .varX => .varX
  | .atom t => .atom (f t)
  | .imp A B => .imp (mapTerms f A) (mapTerms f B)
  | .all ρ A => .all ρ (mapTerms f A)

def observe : Formula → View
  | .bot => .bot
  | .varX => .varX
  | .atom t => .atom t
  | .imp A B => .imp (observe A) (observe B)
  | .all x A => .all x.ty (mapTerms (Term.lam x) (observe A))

def atoms : View → List Term
  | .bot | .varX => []
  | .atom t => [t]
  | .imp A B => atoms A ++ atoms B
  | .all _ A => atoms A

def shapeSize : View → Nat
  | .bot | .varX | .atom _ => 1
  | .imp A B => shapeSize A + shapeSize B + 1
  | .all _ A => shapeSize A + 1

inductive ViewRel : View → View → Prop where
  | bot : ViewRel .bot .bot
  | varX : ViewRel .varX .varX
  | atom {t s : Term} : BetaREq t s → ViewRel (.atom t) (.atom s)
  | imp {A A' B B' : View} : ViewRel A A' → ViewRel B B' → ViewRel (.imp A B) (.imp A' B')
  | all (ρ : Ty) {A B : View} : ViewRel A B → ViewRel (.all ρ A) (.all ρ B)

@[simp] theorem mapTerms_comp (f g : Term → Term) (A : View) :
    mapTerms f (mapTerms g A) = mapTerms (fun t => f (g t)) A := by
  induction A <;> simp_all [mapTerms]

@[simp] theorem mapTerms_id (A : View) : mapTerms (fun t => t) A = A := by
  induction A <;> simp_all [mapTerms]

@[simp] theorem atoms_mapTerms (f : Term → Term) (A : View) :
    atoms (mapTerms f A) = (atoms A).map f := by
  induction A <;> simp_all [mapTerms, atoms]

@[simp] theorem shapeSize_mapTerms (f : Term → Term) (A : View) :
    shapeSize (mapTerms f A) = shapeSize A := by
  induction A <;> simp_all [mapTerms, shapeSize]

@[simp] theorem shapeSize_observe (A : Formula) :
    shapeSize (observe A) = formulaSize A := by
  induction A <;> simp_all [observe, shapeSize, formulaSize]

namespace ViewRel

theorem imp_inv {A A' B B' : View} (h : ViewRel (.imp A B) (.imp A' B')) :
    ViewRel A A' ∧ ViewRel B B' := by
  cases h with | imp hA hB => exact ⟨hA, hB⟩

theorem all_inv {ρ σ : Ty} {A B : View} (h : ViewRel (.all ρ A) (.all σ B)) :
    ρ = σ ∧ ViewRel A B := by
  cases h with | all _ h => exact ⟨rfl, h⟩

theorem size_eq {A B : View} (h : ViewRel A B) : shapeSize A = shapeSize B := by
  induction h <;> simp_all [shapeSize]

theorem refl (A : View) : ViewRel A A := by
  induction A with
  | bot => exact .bot
  | varX => exact .varX
  | atom t => exact .atom (.refl t)
  | imp A B ihA ihB => exact .imp ihA ihB
  | all ρ A ih => exact .all ρ ih

theorem symm {A B : View} (h : ViewRel A B) : ViewRel B A := by
  induction h with
  | bot => exact .bot
  | varX => exact .varX
  | atom h => exact .atom (.symm h)
  | imp _ _ ihA ihB => exact .imp ihA ihB
  | all ρ _ ih => exact .all ρ ih

theorem trans {A B C : View} (h : ViewRel A B) (g : ViewRel B C) : ViewRel A C := by
  induction h generalizing C with
  | bot => cases g; exact .bot
  | varX => cases g; exact .varX
  | atom h => cases g with | atom g => exact .atom (.trans h g)
  | imp hA hB ihA ihB => cases g with | imp gA gB => exact .imp (ihA gA) (ihB gB)
  | all ρ h ih => cases g with | all _ g => exact .all ρ (ih g)

theorem map {A B : View} (h : ViewRel A B) (f g : Term → Term)
    (hfg : ∀ t s, BetaREq t s → BetaREq (f t) (g s)) :
    ViewRel (mapTerms f A) (mapTerms g B) := by
  induction h with
  | bot => exact .bot
  | varX => exact .varX
  | atom h => exact .atom (hfg _ _ h)
  | imp _ _ ihA ihB => exact .imp ihA ihB
  | all ρ _ ih => exact .all ρ ih

end ViewRel

theorem mapTerms_pointwise (A : View) (f g : Term → Term)
    (h : ∀ t ∈ atoms A, BetaREq (f t) (g t)) :
    ViewRel (mapTerms f A) (mapTerms g A) := by
  induction A with
  | bot => exact .bot
  | varX => exact .varX
  | atom t => exact .atom (h t (List.mem_singleton_self t))
  | imp A B ihA ihB =>
      exact .imp (ihA (fun t ht => h t (List.mem_append_left _ ht)))
        (ihB (fun t ht => h t (List.mem_append_right _ ht)))
  | all ρ A ih => exact .all ρ (ih h)

theorem observe_rename (A : Formula) (x y : Var) :
    observe (renameFreeVarFormula A x y) =
      mapTerms (fun t => renameFreeVar t x y) (observe A) := by
  induction A with
  | bot | varX | atom => rfl
  | imp A B ihA ihB => simp only [renameFreeVarFormula, observe, mapTerms, ihA, ihB]
  | all v A ih =>
      by_cases h : v = x
      · subst v
        simp only [renameFreeVarFormula, beq_self_eq_true, ↓reduceIte, observe, mapTerms,
          mapTerms_comp]
        have hf : (fun t => renameFreeVar (.lam x t) x y) = Term.lam x := by
          funext t
          simp [renameFreeVar]
        rw [hf]
      · have hb : (v == x) = false := beq_eq_false_iff_ne.mpr h
        simp only [renameFreeVarFormula, hb, Bool.false_eq_true, ↓reduceIte, observe,
          mapTerms, ih, mapTerms_comp]
        have hf : (fun t => renameFreeVar (.lam v t) x y) =
            (fun t => Term.lam v (renameFreeVar t x y)) := by
          funext t
          simp [renameFreeVar, h]
        rw [hf]

theorem atom_allVars (A : Formula) (t : Term) (ht : t ∈ atoms (observe A))
    (z : Var) (hz : z ∈ allVarsTerm t) : z ∈ allVarsFormula A := by
  induction A generalizing t with
  | bot | varX => cases ht
  | atom s =>
      have hts : t = s := List.mem_singleton.mp ht
      simpa [hts, allVarsFormula] using hz
  | imp A B ihA ihB =>
      simp only [observe, atoms, List.mem_append] at ht
      rcases ht with ht | ht
      · exact List.mem_append_left _ (ihA t ht hz)
      · exact List.mem_append_right _ (ihB t ht hz)
  | all x A ih =>
      simp only [observe, atoms, atoms_mapTerms, List.mem_map] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      simp only [allVarsTerm, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih s hs hz)

theorem atom_freeVars (A : Formula) (t : Term) (ht : t ∈ atoms (observe A))
    (z : Var) (hz : z ∈ freeVarOccurrences t) : z ∈ freeVarsFormula A := by
  induction A generalizing t with
  | bot | varX => cases ht
  | atom s =>
      have hts : t = s := List.mem_singleton.mp ht
      simpa [hts, freeVarsFormula, freeVars, mem_eraseDups_iff] using hz
  | imp A B ihA ihB =>
      simp only [observe, atoms, List.mem_append] at ht
      simp only [freeVarsFormula, mem_eraseDups_iff, List.mem_append]
      rcases ht with ht | ht
      · exact .inl (ihA t ht hz)
      · exact .inr (ihB t ht hz)
  | all x A ih =>
      simp only [observe, atoms, atoms_mapTerms, List.mem_map] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      simp only [freeVarOccurrences, List.mem_filter, bne_iff_ne] at hz
      exact List.mem_filter.mpr ⟨ih s hs hz.1, by simpa using hz.2⟩

end BBS2002.V2.FormulaView


/- Local checked proof module: FormulaConversion -/

namespace BBS2002.V2.FormulaConversion

open FormulaView

theorem observe_subst (A : Formula) (x : Var) (r : Term) :
    ViewRel (observe (substFormula A x r))
      (mapTerms (fun t ↦ substTerm t x r) (observe A)) := by
  match A with
  | .bot => simp only [substFormula]; exact .bot
  | .varX => simp only [substFormula]; exact .varX
  | .atom t => simp only [substFormula]; exact .atom (.refl _)
  | .imp A B =>
      simp only [substFormula, observe, mapTerms]
      exact .imp (observe_subst A x r) (observe_subst B x r)
  | .all v A =>
      rw [substFormula.eq_def (.all v A) x r]
      dsimp only
      split
      · rename_i hvx
        have hv : v = x := beq_iff_eq.mp hvx
        subst v
        simp only [observe, mapTerms, mapTerms_comp]
        exact .all x.ty (mapTerms_pointwise (observe A) _ _
          (fun t _ ↦ by simp only [substTerm, beq_self_eq_true, ↓reduceIte]; exact .refl _))
      · rename_i hvx
        have hv : v ≠ x := by simpa only [beq_iff_eq] using hvx
        split
        · let u : Var := ⟨max (maxVarIdFormula A) (max (maxVarIdTerm r) x.id) + 1, v.ty⟩
          have ih := observe_subst (renameFreeVarFormula A v u) x r
          change ViewRel (.all u.ty (mapTerms (Term.lam u)
            (observe (substFormula (renameFreeVarFormula A v u) x r)))) _
          refine .all v.ty (.trans (ih.map (Term.lam u) (Term.lam u)
            (fun _ _ h ↦ .lam u h)) ?_)
          have huA : u ∉ allVarsFormula A := not_mem_allVarsFormula_of_gt A u
            (Nat.lt_succ_of_le (Nat.le_max_left _ _))
          have hur : u ∉ freeVarOccurrences r := fun h ↦
            not_mem_allVarsTerm_of_gt r u
              (Nat.lt_succ_of_le (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
              (mem_freeVarOccurrences_of_mem_allVars h)
          have hux : u ≠ x := fun h ↦
            Nat.ne_of_gt
              (Nat.lt_succ_of_le (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
              (congrArg Var.id h)
          simp only [observe_rename, mapTerms_comp]
          apply mapTerms_pointwise
          intro t ht
          have h := Conversion.subst_term_congr x
            (.symm (.of_alpha (.lam_rename v u t rfl
              (.inr (fun hu ↦ huA (atom_allVars A t ht u hu)))))) (.refl r)
          rw [substTerm.eq_def (.lam u (renameFreeVar t v u)) x r] at h
          simpa only [beq_eq_false_iff_ne.mpr hux, Bool.false_eq_true, ↓reduceIte, hur] using h
        · rename_i hvr
          refine .all v.ty (.trans ((observe_subst A x r).map (Term.lam v) (Term.lam v)
            (fun _ _ h ↦ .lam v h)) ?_)
          simp only [mapTerms_comp]
          exact mapTerms_pointwise (observe A) _ _ (fun t _ ↦ by
            rw [substTerm.eq_def (.lam v t) x r]
            simp only [beq_eq_false_iff_ne.mpr hv, Bool.false_eq_true, ↓reduceIte, hvr]
            exact .refl _)
termination_by formulaSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [formulaSize, renameFreeVarFormula_size]
  all_goals omega

theorem observe_betaREq {A B : Formula} (h : FormulaBetaREq A B) :
    ViewRel (observe A) (observe B) := by
  induction h with
  | refl A => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | bot => exact .bot
  | varX => exact .varX
  | atom h => exact .atom h
  | imp _ _ ih₁ ih₂ => exact .imp ih₁ ih₂
  | all x _ ih => exact .all x.ty (ih.map (Term.lam x) (Term.lam x) (fun _ _ h ↦ .lam x h))
  | all_rename x y A hty hy =>
      simp only [observe, observe_rename, mapTerms_comp]
      rw [hty]
      exact .all y.ty (mapTerms_pointwise (observe A) _ _ (fun t ht ↦
        .of_alpha (.lam_rename x y t hty (hy.imp_right (fun hy hy' ↦ hy (atom_allVars A t ht y hy'))))))

theorem exists_fresh_var (xs : List Var) (ρ : Ty) :
    ∃ x : Var, x.ty = ρ ∧ x ∉ xs := by
  have bound : ∀ x ∈ xs, x.id ≤ xs.foldr (fun v n ↦ max v.id n) 0 := by
    induction xs with
    | nil => simp
    | cons v vs ih =>
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih x hx) (Nat.le_max_right _ _)
  refine ⟨⟨xs.foldr (fun v n ↦ max v.id n) 0 + 1, ρ⟩, rfl, ?_⟩
  intro hx
  have h := bound _ hx
  dsimp only at h
  omega


theorem view_all_inv {ρ σ : Ty} {A B : View} (h : ViewRel (.all ρ A) (.all σ B)) :
    ρ = σ ∧ ViewRel A B := by
  cases h with
  | all _ h => exact ⟨rfl, h⟩

theorem view_lam_subst {A B : View} (x y : Var) (r : Term)
    (h : ViewRel (mapTerms (Term.lam x) A) (mapTerms (Term.lam y) B)) :
    ViewRel (mapTerms (fun t ↦ substTerm t x r) A)
      (mapTerms (fun t ↦ substTerm t y r) B) := by
  have hApp := h.map (fun t ↦ .app t r) (fun t ↦ .app t r)
    (fun _ _ h ↦ .app h (.refl r))
  simp only [mapTerms_comp] at hApp
  exact (mapTerms_pointwise A _ _ (fun t _ ↦ .symm (.of_conv (.beta x t r)))).trans
    (hApp.trans (mapTerms_pointwise B _ _ (fun t _ ↦ .of_conv (.beta y t r))))

theorem betaREq_of_observe (A B : Formula) (h : ViewRel (observe A) (observe B)) :
    FormulaBetaREq A B := by
  match A, B with
  | .bot, .bot => exact .bot
  | .varX, .varX => exact .varX
  | .atom t, .atom s => cases h with | atom h => exact .atom h
  | .imp A₁ A₂, .imp B₁ B₂ =>
      cases h with
      | imp h₁ h₂ => exact .imp (betaREq_of_observe A₁ B₁ h₁) (betaREq_of_observe A₂ B₂ h₂)
  | .all x A, .all y B =>
      have hparts : x.ty = y.ty ∧ ViewRel (mapTerms (Term.lam x) (observe A))
          (mapTerms (Term.lam y) (observe B)) := view_all_inv h
      obtain ⟨z, hzTy, hz⟩ := exists_fresh_var (allVarsFormula A ++ allVarsFormula B) x.ty
      have hView := (observe_subst A x (.var z)).trans
        ((view_lam_subst x y (.var z) hparts.2).trans (observe_subst B y (.var z)).symm)
      exact all_betaREq_of_fresh_subst A B x y z hzTy.symm (hparts.1.symm.trans hzTy.symm)
        (fun hzA ↦ hz (List.mem_append_left _ hzA))
        (fun hzB ↦ hz (List.mem_append_right _ hzB))
        (betaREq_of_observe (substFormula A x (.var z)) (substFormula B y (.var z)) hView)
  | .bot, .varX => cases h
  | .bot, .atom _ => cases h
  | .bot, .imp _ _ => cases h
  | .bot, .all _ _ => cases h
  | .varX, .bot => cases h
  | .varX, .atom _ => cases h
  | .varX, .imp _ _ => cases h
  | .varX, .all _ _ => cases h
  | .atom _, .bot => cases h
  | .atom _, .varX => cases h
  | .atom _, .imp _ _ => cases h
  | .atom _, .all _ _ => cases h
  | .imp _ _, .bot => cases h
  | .imp _ _, .varX => cases h
  | .imp _ _, .atom _ => cases h
  | .imp _ _, .all _ _ => cases h
  | .all _ _, .bot => cases h
  | .all _ _, .varX => cases h
  | .all _ _, .atom _ => cases h
  | .all _ _, .imp _ _ => cases h
termination_by formulaSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [formulaSize, Conversion.formulaSize_subst]
  all_goals omega

theorem subst_formula_congr {A B : Formula} {r s : Term} (x : Var)
    (hAB : FormulaBetaREq A B) (hrs : BetaREq r s) :
    FormulaBetaREq (substFormula A x r) (substFormula B x s) :=
  betaREq_of_observe _ _ ((observe_subst A x r).trans
    (((observe_betaREq hAB).map (fun t ↦ substTerm t x r) (fun t ↦ substTerm t x s)
      (fun _ _ h ↦ Conversion.subst_term_congr x h hrs)).trans (observe_subst B x s).symm))

theorem observe_subst_twice (A : Formula) (c x : Var) (r t : Term) :
    ViewRel (observe (substFormula (substFormula A c r) x t))
      (mapTerms (fun q ↦ substTerm (substTerm q c r) x t) (observe A)) := by
  have h := (observe_subst (substFormula A c r) x t).trans
    ((observe_subst A c r).map (fun q ↦ substTerm q x t) (fun q ↦ substTerm q x t)
      (fun _ _ h ↦ Conversion.subst_term_congr x h (.refl t)))
  simpa only [mapTerms_comp] using h

theorem subst_formula_comprehension (A : Formula) (c x : Var) (r t : Term)
    (hx : x = c ∨ x ∉ freeVarsFormula A) :
    FormulaBetaREq (substFormula (substFormula A c r) x t)
      (substFormula A c (substTerm r x t)) :=
  betaREq_of_observe _ _ ((observe_subst_twice A c x r t).trans
    ((mapTerms_pointwise (observe A) _ _ (fun q hq ↦
      Conversion.subst_term_comprehension q c x r t
        (hx.imp_right (fun hx hxq ↦ hx (atom_freeVars A q hq x hxq))))).trans
      (observe_subst A c (substTerm r x t)).symm))

theorem subst_formula_compose (A : Formula) (c x : Var) (r t : Term)
    (hcx : c ≠ x) (hct : c ∉ freeVarOccurrences t) :
    FormulaBetaREq (substFormula (substFormula A c r) x t)
      (substFormula (substFormula A x t) c (substTerm r x t)) :=
  betaREq_of_observe _ _ ((observe_subst_twice A c x r t).trans
    ((mapTerms_pointwise (observe A) _ _ (fun q _ ↦
      Conversion.subst_term_compose q c x r t hcx hct)).trans
      (observe_subst_twice A x c t (substTerm r x t)).symm))

theorem subst_formula_commute_var (A : Formula) (v z x : Var) (t : Term)
    (hvx : v ≠ x) (hzx : z ≠ x) (hvt : v ∉ freeVarOccurrences t) :
    FormulaBetaREq (substFormula (substFormula A v (.var z)) x t)
      (substFormula (substFormula A x t) v (.var z)) :=
  betaREq_of_observe _ _ ((observe_subst_twice A v x (.var z) t).trans
    ((mapTerms_pointwise (observe A) _ _ (fun q _ ↦
      Conversion.subst_term_commute_var q v z x t hvx hzx hvt)).trans
      (observe_subst_twice A x v t (.var z)).symm))

theorem imp_inversion {A B C D : Formula} (h : FormulaBetaREq (.imp A B) (.imp C D)) :
    FormulaBetaREq A C ∧ FormulaBetaREq B D := by
  have hView := observe_betaREq h
  cases hView with
  | imp hA hB => exact ⟨betaREq_of_observe A C hA, betaREq_of_observe B D hB⟩

theorem all_inversion {x y : Var} {A B : Formula}
    (h : FormulaBetaREq (.all x A) (.all y B)) :
    x.ty = y.ty ∧ ∀ t : Term, FormulaBetaREq (substFormula A x t) (substFormula B y t) := by
  have hp := view_all_inv (observe_betaREq h)
  refine ⟨hp.1, fun t ↦ ?_⟩
  exact betaREq_of_observe _ _ ((observe_subst A x t).trans
    ((view_lam_subst x y t hp.2).trans (observe_subst B y t).symm))

end BBS2002.V2.FormulaConversion


/- Local checked proof module: MrFreshness -/

namespace BBS2002.V2

theorem freshVar_not_mem_allVars_right {ν : Ty} (comp : CompTerm ν) (r : Option Term)
    (A B : Formula) (ρ : Ty) :
    freshVar comp r A B ρ ∉ allVarsFormula B := by
  apply not_mem_allVarsFormula_of_gt
  simp only [freshVar, freshMrVarId]
  exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))

theorem freshVar_not_mem_compBody {ν : Ty} (comp : CompTerm ν) (r : Option Term)
    (A B : Formula) (ρ : Ty) :
    freshVar comp r A B ρ ∉ allVarsFormula comp.body := by
  apply not_mem_allVarsFormula_of_gt
  simp only [freshVar, freshMrVarId]
  exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))

theorem freshVar_ne_compVar {ν : Ty} (comp : CompTerm ν) (r : Option Term)
    (A B : Formula) (ρ : Ty) : freshVar comp r A B ρ ≠ comp.var := by
  have hlt : comp.var.id < (freshVar comp r A B ρ).id := by
    simp only [freshVar, freshMrVarId]
    exact Nat.lt_succ_of_le (Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _))
  exact fun h => (Nat.ne_of_lt hlt) (congrArg Var.id h).symm

theorem freshVar_not_mem_realizer {ν : Ty} (comp : CompTerm ν) (t : Term)
    (A B : Formula) (ρ : Ty) :
    freshVar comp (some t) A B ρ ∉ allVarsTerm t := by
  apply not_mem_allVarsTerm_of_gt
  simp only [freshVar, freshMrVarId]
  exact Nat.lt_succ_of_le (Nat.le_trans
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _))

theorem mem_freeVarsFormula_allVars {A : Formula} {x : Var}
    (h : x ∈ freeVarsFormula A) : x ∈ allVarsFormula A := by
  induction A with
  | bot | varX => cases h
  | atom t =>
      apply mem_freeVarOccurrences_of_mem_allVars
      simpa only [freeVarsFormula, freeVars, mem_eraseDups_iff] using h
  | imp A B ihA ihB =>
      simp only [freeVarsFormula, mem_eraseDups_iff, List.mem_append] at h
      rcases h with h | h
      · exact List.mem_append_left _ (ihA h)
      · exact List.mem_append_right _ (ihB h)
  | all v A ih => exact List.mem_cons_of_mem _ (ih (List.mem_filter.mp h).1)

theorem freshVar_not_free_compBody {ν : Ty} (comp : CompTerm ν) (r : Option Term)
    (A B : Formula) (ρ : Ty) :
    freshVar comp r A B ρ ∉ freeVarsFormula comp.body := by
  exact fun h => freshVar_not_mem_compBody comp r A B ρ
    (mem_freeVarsFormula_allVars h)

end BBS2002.V2


/- Local checked proof module: MrInductionBase -/

namespace BBS2002.V2

theorem formula_subst_betaREq_of_not_free (A : Formula) (x : Var) (t : Term)
    (hx : x ∉ freeVarsFormula A) : FormulaBetaREq (substFormula A x t) A := by
  apply FormulaConversion.betaREq_of_observe
  refine (FormulaConversion.observe_subst A x t).trans ?_
  have h := FormulaView.mapTerms_pointwise (FormulaView.observe A)
    (fun a ↦ substTerm a x t) (fun a ↦ a)
    (fun a ha ↦ BetaREq.of_alpha (substTerm_alphaEq_of_not_free a x t
      (fun hxa ↦ hx (FormulaView.atom_freeVars A a ha x hxa))))
  simpa only [FormulaView.mapTerms_id] using h

def MRCompatible (ν : Ty) (comp : CompTerm ν) (A : Formula) : Prop :=
  ∀ (B : Formula), FormulaBetaREq A B →
    ∀ (r : Realizer (tau ν A)) (s : Realizer (tau ν B)),
      Option.Rel BetaREq r.toOption s.toOption →
      FormulaBetaREq (mrFormula ν comp A r) (mrFormula ν comp B s)

def MRSubstitution (ν : Ty) (comp : CompTerm ν) (A : Formula) : Prop :=
  ∀ (r : Realizer (tau ν A)) (x : Var) (t : Term),
    (x = comp.var ∨ x ∉ freeVarsFormula comp.body) →
    FormulaBetaREq (substFormula (mrFormula ν comp A r) x t)
      (mrFormula ν comp (substFormula A x t)
        (Realizer.cast (tau_substFormula ν A x t).symm (Realizer.subst r x t)))

theorem mr_subst_fresh_source (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (hc : MRCompatible ν comp A) (hs : MRSubstitution ν comp A)
    (r : Realizer (tau ν A)) (x : Var) (t : Term)
    (hxA : x ∉ freeVarsFormula A)
    (hxC : x = comp.var ∨ x ∉ freeVarsFormula comp.body) :
    FormulaBetaREq (substFormula (mrFormula ν comp A r) x t)
      (mrFormula ν comp A (Realizer.subst r x t)) := by
  refine (hs r x t hxC).trans ?_
  apply FormulaBetaREq.symm
  apply hc (substFormula A x t) (formula_subst_betaREq_of_not_free A x t hxA).symm
  rw [Realizer.toOption_cast]
  exact Realizer.toOption_rel_refl _

end BBS2002.V2


/- Local checked proof module: MrBinderLaws -/

namespace BBS2002.V2

theorem mrFormula_imp_none_none (ν : Ty) (comp : CompTerm ν) (A B : Formula)
    (hA : tau ν A = none) (hB : tau ν B = none)
    (r : Realizer (tau ν (.imp A B))) :
    mrFormula ν comp (.imp A B) r =
      .imp (mrFormula ν comp A (Realizer.cast (τ := none) hA.symm ()))
        (mrFormula ν comp B (Realizer.cast (τ := none) hB.symm ())) := by
  rw [mrFormula.eq_def ν comp (.imp A B) r]
  dsimp only
  split <;> rename_i ha hb
  all_goals
    have ea := hA.symm.trans ha
    have eb := hB.symm.trans hb
    cases ea <;> cases eb <;> rfl

theorem mrFormula_imp_none_some (ν : Ty) (comp : CompTerm ν) (A B : Formula)
    (σ : Ty) (hA : tau ν A = none) (hB : tau ν B = some σ)
    (r : Realizer (tau ν (.imp A B))) :
    mrFormula ν comp (.imp A B) r =
      .imp (mrFormula ν comp A (Realizer.cast (τ := none) hA.symm ()))
        (mrFormula ν comp B (Realizer.cast (by simp only [tau, hA]) r)) := by
  rw [mrFormula.eq_def ν comp (.imp A B) r]
  dsimp only
  split <;> rename_i ha hb
  all_goals
    have ea := hA.symm.trans ha
    have eb := hB.symm.trans hb
    cases ea <;> cases eb <;> rfl

theorem mrFormula_imp_some_none (ν : Ty) (comp : CompTerm ν) (A B : Formula)
    (ρ : Ty) (hA : tau ν A = some ρ) (hB : tau ν B = none)
    (r : Realizer (tau ν (.imp A B))) :
    let y := freshVar comp none A B ρ
    mrFormula ν comp (.imp A B) r =
      .all y (.imp
        (mrFormula ν comp A (Realizer.cast (τ := some ρ) hA.symm (Term.var y)))
        (mrFormula ν comp B (Realizer.cast (τ := none) hB.symm ()))) := by
  rw [mrFormula.eq_def ν comp (.imp A B) r]
  dsimp only
  split <;> rename_i ha hb
  all_goals
    have ea := hA.symm.trans ha
    have eb := hB.symm.trans hb
    cases ea <;> cases eb <;> rfl

theorem mrFormula_imp_some_some (ν : Ty) (comp : CompTerm ν) (A B : Formula)
    (ρ σ : Ty) (hA : tau ν A = some ρ) (hB : tau ν B = some σ)
    (r : Realizer (tau ν (.imp A B))) :
    let f : Realizer (some (.arr ρ σ)) := Realizer.cast (by simp only [tau, hA, hB]) r
    let y := freshVar comp (some f) A B ρ
    mrFormula ν comp (.imp A B) r =
      .all y (.imp
        (mrFormula ν comp A (Realizer.cast (τ := some ρ) hA.symm (Term.var y)))
        (mrFormula ν comp B (Realizer.cast (τ := some σ) hB.symm (Term.app f (.var y))))) := by
  rw [mrFormula.eq_def ν comp (.imp A B) r]
  dsimp only
  split <;> rename_i ha hb
  all_goals
    have ea := hA.symm.trans ha
    have eb := hB.symm.trans hb
    cases ea <;> cases eb <;> rfl

theorem mrFormula_all_none (ν : Ty) (comp : CompTerm ν) (x : Var) (A : Formula)
    (hA : tau ν A = none) (r : Realizer (tau ν (.all x A))) :
    let y := freshVar comp r.toOption (.all x A) .bot x.ty
    mrFormula ν comp (.all x A) r =
      .all y (mrFormula ν comp (renameFreeVarFormula A x y)
        (Realizer.cast (τ := none)
          ((tau_renameFreeVarFormula ν A x y).trans hA).symm ())) := by
  rw [mrFormula.eq_def ν comp (.all x A) r]
  dsimp only
  split <;> rename_i ha
  all_goals
    have ea := hA.symm.trans ha
    cases ea <;> rfl

theorem mrFormula_all_some (ν : Ty) (comp : CompTerm ν) (x : Var) (A : Formula)
    (ρ : Ty) (hA : tau ν A = some ρ) (r : Realizer (tau ν (.all x A))) :
    let y := freshVar comp r.toOption (.all x A) .bot x.ty
    let f : Realizer (some (.arr x.ty ρ)) := Realizer.cast (by simp only [tau, hA]) r
    mrFormula ν comp (.all x A) r =
      .all y (mrFormula ν comp (renameFreeVarFormula A x y)
        (Realizer.cast (τ := some ρ)
          ((tau_renameFreeVarFormula ν A x y).trans hA).symm (Term.app f (.var y)))) := by
  rw [mrFormula.eq_def ν comp (.all x A) r]
  dsimp only
  split <;> rename_i ha
  all_goals
    have ea := hA.symm.trans ha
    cases ea <;> rfl

theorem all_betaREq_of_all_subst (A B : Formula) (x y : Var) (hxy : x.ty = y.ty)
    (h : ∀ z : Var, z.ty = x.ty →
      FormulaBetaREq (substFormula A x (.var z)) (substFormula B y (.var z))) :
    FormulaBetaREq (.all x A) (.all y B) := by
  obtain ⟨z, hzt, hz⟩ := FormulaConversion.exists_fresh_var
    (allVarsFormula A ++ allVarsFormula B) x.ty
  have hzA : z ∉ allVarsFormula A := fun h ↦ hz (List.mem_append_left _ h)
  have hzB : z ∉ allVarsFormula B := fun h ↦ hz (List.mem_append_right _ h)
  exact all_betaREq_of_fresh_subst A B x y z hzt.symm (hxy.symm.trans hzt.symm)
    hzA hzB (h z hzt)

theorem option_rel_subst_app_var (r : Option Term) (x : Var) (t : Term)
    (hr : ∀ f ∈ r, x ∉ freeVars f) :
    Option.Rel BetaREq
      ((r.map (fun f ↦ Term.app f (.var x))).map (fun q ↦ substTerm q x t))
      (r.map (fun f ↦ Term.app f t)) := by
  cases r with
  | none => exact .none
  | some f =>
      apply Option.Rel.some
      simp only [substTerm, beq_self_eq_true, ↓reduceIte]
      apply BetaREq.app _ (.refl t)
      exact .of_alpha (substTerm_alphaEq_of_not_free f x t
        (fun hx ↦ hr f rfl (mem_eraseDups_of_mem' _ hx)))

theorem applyImp_toOption_some_arg (ν : Ty) (A B : Formula)
    (r : Realizer (tau ν (.imp A B))) (a : Realizer (tau ν A)) (t : Term)
    (ha : a.toOption = some t) :
    (Realizer.applyImp ν A B r a).toOption = r.toOption.map (fun f ↦ Term.app f t) := by
  rw [Realizer.applyImp_toOption, ha]
  cases r.toOption <;> rfl

theorem option_betaRel_symm {r s : Option Term} (h : Option.Rel BetaREq r s) :
    Option.Rel BetaREq s r := by
  cases h with
  | none => exact .none
  | some h => exact .some h.symm

theorem option_betaRel_trans {r s t : Option Term}
    (h : Option.Rel BetaREq r s) (g : Option.Rel BetaREq s t) :
    Option.Rel BetaREq r t := by
  cases h with
  | none => cases g; exact .none
  | some h => cases g with | some g => exact .some (.trans h g)

theorem Realizer.eq_of_toOption_eq {τ : Option Ty} (r s : Realizer τ)
    (h : r.toOption = s.toOption) : r = s := by
  cases τ with
  | none => cases r; cases s; rfl
  | some ρ => exact Option.some.inj h

theorem Realizer.toOption_eq_none {τ : Option Ty} (r : Realizer τ) (hτ : τ = none) :
    r.toOption = none := by
  cases hτ
  rfl

theorem mr_imp_binder_congr (ν : Ty) (comp : CompTerm ν) (A B : Formula)
    (hA : MRCompatible ν comp A ∧ MRSubstitution ν comp A)
    (hB : MRCompatible ν comp B ∧ MRSubstitution ν comp B)
    (r : Realizer (tau ν (.imp A B))) (u z : Var) (huz : u.ty = z.ty)
    (a : Realizer (tau ν A)) (b : Realizer (tau ν A))
    (ha : a.toOption = some (.var u)) (hb : b.toOption = some (.var z))
    (huA : u ∉ freeVarsFormula A) (huB : u ∉ freeVarsFormula B)
    (huR : ∀ f ∈ r.toOption, u ∉ freeVars f)
    (huC : u = comp.var ∨ u ∉ freeVarsFormula comp.body)
    (hzA : z ∉ freeVarsFormula A) (hzB : z ∉ freeVarsFormula B)
    (hzR : ∀ f ∈ r.toOption, z ∉ freeVars f)
    (hzC : z = comp.var ∨ z ∉ freeVarsFormula comp.body) :
    FormulaBetaREq
      (.all u (.imp (mrFormula ν comp A a)
        (mrFormula ν comp B (Realizer.applyImp ν A B r a))))
      (.all z (.imp (mrFormula ν comp A b)
        (mrFormula ν comp B (Realizer.applyImp ν A B r b)))) := by
  apply all_betaREq_of_all_subst _ _ u z huz
  intro k hk
  simp only [substFormula_imp]
  apply FormulaBetaREq.imp
  · refine (mr_subst_fresh_source ν comp A hA.1 hA.2 a u (.var k) huA huC).trans ?_
    refine FormulaBetaREq.trans ?_
      (mr_subst_fresh_source ν comp A hA.1 hA.2 b z (.var k) hzA hzC).symm
    apply hA.1 A (.refl A)
    rw [Realizer.subst_toOption, Realizer.subst_toOption, ha, hb]
    simp only [Option.map_some, substTerm, beq_self_eq_true, ↓reduceIte]
    exact .some (.refl _)
  · refine (mr_subst_fresh_source ν comp B hB.1 hB.2
      (Realizer.applyImp ν A B r a) u (.var k) huB huC).trans ?_
    refine FormulaBetaREq.trans ?_
      (mr_subst_fresh_source ν comp B hB.1 hB.2
        (Realizer.applyImp ν A B r b) z (.var k) hzB hzC).symm
    apply hB.1 B (.refl B)
    rw [Realizer.subst_toOption, Realizer.subst_toOption,
      applyImp_toOption_some_arg ν A B r a (.var u) ha,
      applyImp_toOption_some_arg ν A B r b (.var z) hb]
    exact option_betaRel_trans (option_rel_subst_app_var r.toOption u (.var k) huR)
      (option_betaRel_symm (option_rel_subst_app_var r.toOption z (.var k) hzR))

theorem mrFormula_imp_none (ν : Ty) (comp : CompTerm ν) (A B : Formula)
    (hA : tau ν A = none) (r : Realizer (tau ν (.imp A B))) (a : Realizer (tau ν A)) :
    mrFormula ν comp (.imp A B) r =
      .imp (mrFormula ν comp A a) (mrFormula ν comp B (Realizer.applyImp ν A B r a)) := by
  have ha : Realizer.cast (τ := none) hA.symm () = a :=
    Realizer.eq_of_toOption_eq _ _
      ((Realizer.toOption_cast (τ := none) hA.symm ()).trans
        (Realizer.toOption_eq_none a hA).symm)
  cases hB : tau ν B with
  | none =>
      rw [mrFormula_imp_none_none ν comp A B hA hB r, ha]
      congr 1
      apply congrArg (mrFormula ν comp B)
      apply Realizer.eq_of_toOption_eq
      exact (Realizer.toOption_cast (τ := none) hB.symm ()).trans
        (Realizer.toOption_eq_none _ hB).symm
  | some σ =>
      rw [mrFormula_imp_none_some ν comp A B σ hA hB r, ha]
      congr 1
      apply congrArg (mrFormula ν comp B)
      apply Realizer.eq_of_toOption_eq
      rw [Realizer.toOption_cast, Realizer.applyImp_toOption, Realizer.toOption_eq_none a hA]
      cases r.toOption <;> rfl

theorem mrFormula_imp_some (ν : Ty) (comp : CompTerm ν) (A B : Formula)
    (ρ : Ty) (hA : tau ν A = some ρ) (r : Realizer (tau ν (.imp A B))) :
    let y := freshVar comp r.toOption A B ρ
    let a : Realizer (tau ν A) := Realizer.cast (τ := some ρ) hA.symm (Term.var y)
    mrFormula ν comp (.imp A B) r =
      .all y (.imp (mrFormula ν comp A a)
        (mrFormula ν comp B (Realizer.applyImp ν A B r a))) := by
  dsimp only
  cases hB : tau ν B with
  | none =>
      have hr : r.toOption = none :=
        Realizer.toOption_eq_none r (by simp only [tau, hA, hB])
      rw [mrFormula_imp_some_none ν comp A B ρ hA hB r, hr]
      congr 1
      congr 1
      apply congrArg (mrFormula ν comp B)
      apply Realizer.eq_of_toOption_eq
      exact (Realizer.toOption_cast (τ := none) hB.symm ()).trans
        (Realizer.toOption_eq_none _ hB).symm
  | some σ =>
      let f : Realizer (some (.arr ρ σ)) :=
        Realizer.cast (by simp only [tau, hA, hB]) r
      let y := freshVar comp (some f) A B ρ
      let a : Realizer (tau ν A) := Realizer.cast (τ := some ρ) hA.symm (Term.var y)
      have hr : r.toOption = some f :=
        (Realizer.toOption_cast (σ := some (.arr ρ σ))
          (by simp only [tau, hA, hB]) r).symm
      have ha : a.toOption = some (.var y) :=
        Realizer.toOption_cast (τ := some ρ) hA.symm (Term.var y)
      have happ : (Realizer.applyImp ν A B r a).toOption = some (.app f (.var y)) := by
        rw [applyImp_toOption_some_arg ν A B r a (.var y) ha, hr]
        rfl
      rw [mrFormula_imp_some_some ν comp A B ρ σ hA hB r, hr]
      congr 1
      congr 1
      apply congrArg (mrFormula ν comp B)
      apply Realizer.eq_of_toOption_eq
      exact (Realizer.toOption_cast (τ := some σ) hB.symm (Term.app f (.var y))).trans
        happ.symm

theorem mr_imp_fresh (ν : Ty) (comp : CompTerm ν) (A B : Formula)
    (hAP : MRCompatible ν comp A ∧ MRSubstitution ν comp A)
    (hBP : MRCompatible ν comp B ∧ MRSubstitution ν comp B)
    (ρ : Ty) (hA : tau ν A = some ρ) (r : Realizer (tau ν (.imp A B)))
    (z : Var) (hzTy : z.ty = ρ)
    (hzA : z ∉ freeVarsFormula A) (hzB : z ∉ freeVarsFormula B)
    (hzR : ∀ f ∈ r.toOption, z ∉ freeVars f)
    (hzC : z = comp.var ∨ z ∉ freeVarsFormula comp.body) :
    let a : Realizer (tau ν A) := Realizer.cast (τ := some ρ) hA.symm (Term.var z)
    FormulaBetaREq (mrFormula ν comp (.imp A B) r)
      (.all z (.imp (mrFormula ν comp A a)
        (mrFormula ν comp B (Realizer.applyImp ν A B r a)))) := by
  let u := freshVar comp r.toOption A B ρ
  let a : Realizer (tau ν A) := Realizer.cast (τ := some ρ) hA.symm (Term.var u)
  let b : Realizer (tau ν A) := Realizer.cast (τ := some ρ) hA.symm (Term.var z)
  have ha : a.toOption = some (.var u) :=
    Realizer.toOption_cast (τ := some ρ) hA.symm (Term.var u)
  have hb : b.toOption = some (.var z) :=
    Realizer.toOption_cast (τ := some ρ) hA.symm (Term.var z)
  have huA : u ∉ freeVarsFormula A := fun h ↦
    freshVar_not_mem_allVars_left comp r.toOption A B ρ (mem_freeVarsFormula_allVars h)
  have huB : u ∉ freeVarsFormula B := fun h ↦
    freshVar_not_mem_allVars_right comp r.toOption A B ρ (mem_freeVarsFormula_allVars h)
  have huR : ∀ f ∈ r.toOption, u ∉ freeVars f := by
    intro f hf huf
    have hm : u ∈ allVarsTerm f :=
      mem_freeVarOccurrences_of_mem_allVars (mem_eraseDups_iff.mp huf)
    have heq : r.toOption = some f := hf
    apply freshVar_not_mem_realizer comp f A B ρ
    simpa only [u, heq] using hm
  have huC : u = comp.var ∨ u ∉ freeVarsFormula comp.body :=
    .inr (freshVar_not_free_compBody comp r.toOption A B ρ)
  dsimp only
  rw [mrFormula_imp_some ν comp A B ρ hA r]
  exact mr_imp_binder_congr ν comp A B hAP hBP r u z hzTy.symm a b ha hb
    huA huB huR huC hzA hzB hzR hzC

theorem mrFormula_source_eq (ν : Ty) (comp : CompTerm ν) {A B : Formula}
    (h : A = B) (r : Realizer (tau ν A)) (s : Realizer (tau ν B))
    (hrs : r.toOption = s.toOption) : mrFormula ν comp A r = mrFormula ν comp B s := by
  cases h
  exact congrArg (mrFormula ν comp A) (Realizer.eq_of_toOption_eq r s hrs)

theorem mrFormula_all_apply (ν : Ty) (comp : CompTerm ν) (x : Var) (A : Formula)
    (r : Realizer (tau ν (.all x A))) :
    let y := freshVar comp r.toOption (.all x A) .bot x.ty
    mrFormula ν comp (.all x A) r =
      .all y (mrFormula ν comp (substFormula A x (.var y))
        (Realizer.applyAll ν x A r (.var y))) := by
  let y := freshVar comp r.toOption (.all x A) .bot x.ty
  have hyA : y ∉ allVarsFormula A := fun h ↦
    freshVar_not_mem_allVars_left comp r.toOption (.all x A) .bot x.ty
      (List.mem_cons_of_mem x h)
  have heq := Conversion.subst_formula_fresh_var A x y hyA
  cases hA : tau ν A with
  | none =>
      have hr : r.toOption = none :=
        Realizer.toOption_eq_none r (by simp only [tau, hA])
      have hopt : (Realizer.applyAll ν x A r (.var y)).toOption = none := by
        rw [Realizer.applyAll_toOption, hr]
        rfl
      rw [mrFormula_all_none ν comp x A hA r]
      apply congrArg (Formula.all y)
      apply mrFormula_source_eq ν comp heq.symm
      exact (Realizer.toOption_cast (τ := none)
        ((tau_renameFreeVarFormula ν A x y).trans hA).symm ()).trans hopt.symm
  | some ρ =>
      let f : Realizer (some (.arr x.ty ρ)) :=
        Realizer.cast (by simp only [tau, hA]) r
      have hr : r.toOption = some f :=
        (Realizer.toOption_cast (σ := some (.arr x.ty ρ))
          (by simp only [tau, hA]) r).symm
      have hopt : (Realizer.applyAll ν x A r (.var y)).toOption =
          some (.app f (.var y)) := by
        rw [Realizer.applyAll_toOption, hr]
        rfl
      rw [mrFormula_all_some ν comp x A ρ hA r]
      apply congrArg (Formula.all y)
      apply mrFormula_source_eq ν comp heq.symm
      exact (Realizer.toOption_cast (τ := some ρ)
        ((tau_renameFreeVarFormula ν A x y).trans hA).symm (Term.app f (.var y))).trans
        hopt.symm

theorem mr_all_inst_to_common (ν : Ty) (comp : CompTerm ν) (x : Var) (A : Formula)
    (hSmall : ∀ C, formulaSize C < formulaSize (.all x A) →
      MRCompatible ν comp C ∧ MRSubstitution ν comp C)
    (r : Realizer (tau ν (.all x A))) (u : Var) (t : Term)
    (huA : u = x ∨ u ∉ freeVarsFormula A)
    (huR : ∀ f ∈ r.toOption, u ∉ freeVars f)
    (huC : u = comp.var ∨ u ∉ freeVarsFormula comp.body) :
    FormulaBetaREq
      (substFormula (mrFormula ν comp (substFormula A x (.var u))
        (Realizer.applyAll ν x A r (.var u))) u t)
      (mrFormula ν comp (substFormula A x t) (Realizer.applyAll ν x A r t)) := by
  have hSub := (hSmall (substFormula A x (.var u)) (by
    simp only [formulaSize_substFormula, formulaSize]
    omega)).2
  have hCongr := (hSmall (substFormula (substFormula A x (.var u)) u t) (by
    simp only [formulaSize_substFormula, formulaSize]
    omega)).1
  have hSource : FormulaBetaREq (substFormula (substFormula A x (.var u)) u t)
      (substFormula A x t) := by
    simpa only [substTerm, beq_self_eq_true, ↓reduceIte] using
      FormulaConversion.subst_formula_comprehension A x u (.var u) t huA
  refine (hSub (Realizer.applyAll ν x A r (.var u)) u t huC).trans ?_
  apply hCongr (substFormula A x t) hSource
  rw [Realizer.toOption_cast, Realizer.subst_toOption,
    Realizer.applyAll_toOption, Realizer.applyAll_toOption]
  exact option_rel_subst_app_var r.toOption u t huR

theorem mr_all_binder_congr (ν : Ty) (comp : CompTerm ν) (x : Var) (A : Formula)
    (hSmall : ∀ C, formulaSize C < formulaSize (.all x A) →
      MRCompatible ν comp C ∧ MRSubstitution ν comp C)
    (r : Realizer (tau ν (.all x A))) (u z : Var) (huz : u.ty = z.ty)
    (huA : u = x ∨ u ∉ freeVarsFormula A)
    (huR : ∀ f ∈ r.toOption, u ∉ freeVars f)
    (huC : u = comp.var ∨ u ∉ freeVarsFormula comp.body)
    (hzA : z = x ∨ z ∉ freeVarsFormula A)
    (hzR : ∀ f ∈ r.toOption, z ∉ freeVars f)
    (hzC : z = comp.var ∨ z ∉ freeVarsFormula comp.body) :
    FormulaBetaREq
      (.all u (mrFormula ν comp (substFormula A x (.var u))
        (Realizer.applyAll ν x A r (.var u))))
      (.all z (mrFormula ν comp (substFormula A x (.var z))
        (Realizer.applyAll ν x A r (.var z)))) := by
  apply all_betaREq_of_all_subst _ _ u z huz
  intro k hk
  exact (mr_all_inst_to_common ν comp x A hSmall r u (.var k) huA huR huC).trans
    (mr_all_inst_to_common ν comp x A hSmall r z (.var k) hzA hzR hzC).symm

theorem mr_all_fresh (ν : Ty) (comp : CompTerm ν) (x : Var) (A : Formula)
    (hSmall : ∀ C, formulaSize C < formulaSize (.all x A) →
      MRCompatible ν comp C ∧ MRSubstitution ν comp C)
    (r : Realizer (tau ν (.all x A))) (z : Var) (hzTy : z.ty = x.ty)
    (hzA : z ∉ freeVarsFormula (.all x A))
    (hzR : ∀ f ∈ r.toOption, z ∉ freeVars f)
    (hzC : z = comp.var ∨ z ∉ freeVarsFormula comp.body) :
    FormulaBetaREq (mrFormula ν comp (.all x A) r)
      (.all z (mrFormula ν comp (substFormula A x (.var z))
        (Realizer.applyAll ν x A r (.var z)))) := by
  let u := freshVar comp r.toOption (.all x A) .bot x.ty
  have huA : u = x ∨ u ∉ freeVarsFormula A := by
    apply Or.inr
    intro h
    exact freshVar_not_mem_allVars_left comp r.toOption (.all x A) .bot x.ty
      (List.mem_cons_of_mem x (mem_freeVarsFormula_allVars h))
  have huR : ∀ f ∈ r.toOption, u ∉ freeVars f := by
    intro f hf huf
    have hm : u ∈ allVarsTerm f :=
      mem_freeVarOccurrences_of_mem_allVars (mem_eraseDups_iff.mp huf)
    have heq : r.toOption = some f := hf
    apply freshVar_not_mem_realizer comp f (.all x A) .bot x.ty
    simpa only [u, heq] using hm
  have huC : u = comp.var ∨ u ∉ freeVarsFormula comp.body :=
    .inr (freshVar_not_free_compBody comp r.toOption (.all x A) .bot x.ty)
  have hzA' : z = x ∨ z ∉ freeVarsFormula A := by
    by_cases hzx : z = x
    · exact .inl hzx
    · exact .inr (fun hz ↦ hzA (List.mem_filter.mpr ⟨hz, by simpa using hzx⟩))
  rw [mrFormula_all_apply ν comp x A r]
  exact mr_all_binder_congr ν comp x A hSmall r u z hzTy.symm
    huA huR huC hzA' hzR hzC

end BBS2002.V2


/- Local checked proof module: MrCongruenceStep -/

namespace BBS2002.V2

theorem applyImp_option_rel (ν : Ty) (A B C D : Formula)
    (r : Realizer (tau ν (.imp A B))) (s : Realizer (tau ν (.imp C D)))
    (a : Realizer (tau ν A)) (c : Realizer (tau ν C))
    (hrs : Option.Rel BetaREq r.toOption s.toOption)
    (hac : Option.Rel BetaREq a.toOption c.toOption) :
    Option.Rel BetaREq (Realizer.applyImp ν A B r a).toOption
      (Realizer.applyImp ν C D s c).toOption := by
  rw [Realizer.applyImp_toOption, Realizer.applyImp_toOption]
  generalize r.toOption = rr at hrs ⊢
  generalize s.toOption = ss at hrs ⊢
  generalize a.toOption = aa at hac ⊢
  generalize c.toOption = cc at hac ⊢
  cases hrs with
  | none => exact .none
  | some hrs =>
      cases hac with
      | none => exact .some hrs
      | some hac => exact .some (.app hrs hac)

theorem applyAll_option_rel (ν : Ty) (x y : Var) (A B : Formula)
    (r : Realizer (tau ν (.all x A))) (s : Realizer (tau ν (.all y B)))
    (t u : Term) (hrs : Option.Rel BetaREq r.toOption s.toOption) (htu : BetaREq t u) :
    Option.Rel BetaREq (Realizer.applyAll ν x A r t).toOption
      (Realizer.applyAll ν y B s u).toOption := by
  rw [Realizer.applyAll_toOption, Realizer.applyAll_toOption]
  generalize r.toOption = rr at hrs ⊢
  generalize s.toOption = ss at hrs ⊢
  cases hrs with
  | none => exact .none
  | some hrs => exact .some (.app hrs htu)

theorem mr_congruence_imp (ν : Ty) (comp : CompTerm ν) (A B C D : Formula)
    (hA : MRCompatible ν comp A ∧ MRSubstitution ν comp A)
    (hB : MRCompatible ν comp B ∧ MRSubstitution ν comp B)
    (hC : MRCompatible ν comp C ∧ MRSubstitution ν comp C)
    (hD : MRCompatible ν comp D ∧ MRSubstitution ν comp D)
    (hAC : FormulaBetaREq A C) (hBD : FormulaBetaREq B D)
    (r : Realizer (tau ν (.imp A B))) (s : Realizer (tau ν (.imp C D)))
    (hrs : Option.Rel BetaREq r.toOption s.toOption) :
    FormulaBetaREq (mrFormula ν comp (.imp A B) r) (mrFormula ν comp (.imp C D) s) := by
  cases hτA : tau ν A with
  | none =>
      have hτC : tau ν C = none := (tau_formulaBetaREq ν hAC).symm.trans hτA
      let a : Realizer (tau ν A) := Realizer.cast (τ := none) hτA.symm ()
      let c : Realizer (tau ν C) := Realizer.cast (τ := none) hτC.symm ()
      have hac : Option.Rel BetaREq a.toOption c.toOption := by
        rw [Realizer.toOption_eq_none a hτA, Realizer.toOption_eq_none c hτC]
        exact .none
      rw [mrFormula_imp_none ν comp A B hτA r a, mrFormula_imp_none ν comp C D hτC s c]
      exact .imp (hA.1 C hAC a c hac)
        (hB.1 D hBD _ _ (applyImp_option_rel ν A B C D r s a c hrs hac))
  | some ρ =>
      have hτC : tau ν C = some ρ := (tau_formulaBetaREq ν hAC).symm.trans hτA
      obtain ⟨z, hzTy, hz⟩ := FormulaConversion.exists_fresh_var
        (freeVarsFormula A ++ freeVarsFormula B ++ freeVarsFormula C ++ freeVarsFormula D ++
          r.toOption.toList.flatMap freeVars ++ s.toOption.toList.flatMap freeVars ++
          freeVarsFormula comp.body) ρ
      have hzParts : z ∉ freeVarsFormula A ∧ z ∉ freeVarsFormula B ∧
          z ∉ freeVarsFormula C ∧ z ∉ freeVarsFormula D ∧
          z ∉ r.toOption.toList.flatMap freeVars ∧ z ∉ s.toOption.toList.flatMap freeVars ∧
          z ∉ freeVarsFormula comp.body := by
        simpa only [List.mem_append, not_or, and_assoc] using hz
      rcases hzParts with ⟨hzA, hzB, hzC, hzD, hzR, hzS, hzComp⟩
      have hzR' : ∀ f ∈ r.toOption, z ∉ freeVars f := by
        intro f hf hzf
        exact hzR (List.mem_flatMap.mpr ⟨f, by simpa using hf, hzf⟩)
      have hzS' : ∀ f ∈ s.toOption, z ∉ freeVars f := by
        intro f hf hzf
        exact hzS (List.mem_flatMap.mpr ⟨f, by simpa using hf, hzf⟩)
      let a : Realizer (tau ν A) := Realizer.cast (τ := some ρ) hτA.symm (.var z)
      let c : Realizer (tau ν C) := Realizer.cast (τ := some ρ) hτC.symm (.var z)
      have hac : Option.Rel BetaREq a.toOption c.toOption := by
        rw [show a.toOption = some (.var z) from Realizer.toOption_cast _ _,
          show c.toOption = some (.var z) from Realizer.toOption_cast _ _]
        exact .some (.refl _)
      refine (mr_imp_fresh ν comp A B hA hB ρ hτA r z hzTy hzA hzB hzR' (.inr hzComp)).trans ?_
      refine FormulaBetaREq.trans ?_
        (mr_imp_fresh ν comp C D hC hD ρ hτC s z hzTy hzC hzD hzS' (.inr hzComp)).symm
      exact .all z (.imp (hA.1 C hAC a c hac)
        (hB.1 D hBD _ _ (applyImp_option_rel ν A B C D r s a c hrs hac)))

theorem mr_congruence_step (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (hSmall : ∀ C, formulaSize C < formulaSize A →
      MRCompatible ν comp C ∧ MRSubstitution ν comp C) : MRCompatible ν comp A := by
  intro B hAB r s hrs
  have hv := FormulaConversion.observe_betaREq hAB
  match A, B with
  | .bot, .bot =>
      rw [mrFormula.eq_def ν comp .bot r, mrFormula.eq_def ν comp .bot s]
      exact .bot
  | .varX, .varX =>
      rw [mrFormula.eq_def ν comp .varX r, mrFormula.eq_def ν comp .varX s]
      apply FormulaConversion.subst_formula_congr comp.var (.refl comp.body)
      cases hrs with | some h => exact h
  | .atom t, .atom u =>
      rw [mrFormula.eq_def ν comp (.atom t) r, mrFormula.eq_def ν comp (.atom u) s]
      exact hAB
  | .imp A B, .imp C D =>
      have he := FormulaConversion.imp_inversion hAB
      have heA := formulaSize_formulaBetaREq he.1
      have heB := formulaSize_formulaBetaREq he.2
      exact mr_congruence_imp ν comp A B C D
        (hSmall A (by simp only [formulaSize]; omega))
        (hSmall B (by simp only [formulaSize]; omega))
        (hSmall C (by simp only [formulaSize]; omega))
        (hSmall D (by simp only [formulaSize]; omega)) he.1 he.2 r s hrs
  | .all x A, .all y B =>
      have he := FormulaConversion.all_inversion hAB
      have heSize := formulaSize_formulaBetaREq hAB
      have hSmallB : ∀ C, formulaSize C < formulaSize (.all y B) →
          MRCompatible ν comp C ∧ MRSubstitution ν comp C := by
        intro C hC
        apply hSmall C
        omega
      obtain ⟨z, hzTy, hz⟩ := FormulaConversion.exists_fresh_var
        (freeVarsFormula (.all x A) ++ freeVarsFormula (.all y B) ++
          r.toOption.toList.flatMap freeVars ++ s.toOption.toList.flatMap freeVars ++
          freeVarsFormula comp.body) x.ty
      have hzParts : z ∉ freeVarsFormula (.all x A) ∧ z ∉ freeVarsFormula (.all y B) ∧
          z ∉ r.toOption.toList.flatMap freeVars ∧ z ∉ s.toOption.toList.flatMap freeVars ∧
          z ∉ freeVarsFormula comp.body := by
        simpa only [List.mem_append, not_or, and_assoc] using hz
      rcases hzParts with ⟨hzA, hzB, hzR, hzS, hzComp⟩
      have hzR' : ∀ f ∈ r.toOption, z ∉ freeVars f := by
        intro f hf hzf
        exact hzR (List.mem_flatMap.mpr ⟨f, by simpa using hf, hzf⟩)
      have hzS' : ∀ f ∈ s.toOption, z ∉ freeVars f := by
        intro f hf hzf
        exact hzS (List.mem_flatMap.mpr ⟨f, by simpa using hf, hzf⟩)
      refine (mr_all_fresh ν comp x A hSmall r z hzTy hzA hzR' (.inr hzComp)).trans ?_
      refine FormulaBetaREq.trans ?_
        (mr_all_fresh ν comp y B hSmallB s z (hzTy.trans he.1) hzB hzS' (.inr hzComp)).symm
      apply FormulaBetaREq.all z
      exact (hSmall (substFormula A x (.var z))
        (by simp only [formulaSize_substFormula, formulaSize]; omega)).1
        (substFormula B y (.var z)) (he.2 (.var z)) _ _
        (applyAll_option_rel ν x y A B r s (.var z) (.var z) hrs (.refl _))
  | .bot, .varX => cases hv
  | .bot, .atom _ => cases hv
  | .bot, .imp _ _ => cases hv
  | .bot, .all _ _ => cases hv
  | .varX, .bot => cases hv
  | .varX, .atom _ => cases hv
  | .varX, .imp _ _ => cases hv
  | .varX, .all _ _ => cases hv
  | .atom _, .bot => cases hv
  | .atom _, .varX => cases hv
  | .atom _, .imp _ _ => cases hv
  | .atom _, .all _ _ => cases hv
  | .imp _ _, .bot => cases hv
  | .imp _ _, .varX => cases hv
  | .imp _ _, .atom _ => cases hv
  | .imp _ _, .all _ _ => cases hv
  | .all _ _, .bot => cases hv
  | .all _ _, .varX => cases hv
  | .all _ _, .atom _ => cases hv
  | .all _ _, .imp _ _ => cases hv

end BBS2002.V2


/- Local checked proof module: FormulaBinder -/

namespace BBS2002.V2

/-- Express substitution under a quantifier using any sufficiently fresh binder. -/
theorem subst_formula_all_fresh (A : Formula) (v z x : Var) (t : Term)
    (hty : v.ty = z.ty) (hzA : z ∉ allVarsFormula A)
    (hzx : z ≠ x) (hzt : z ∉ freeVarOccurrences t) :
    FormulaBetaREq (substFormula (.all v A) x t)
      (.all z (substFormula (substFormula A v (.var z)) x t)) := by
  have hrename : FormulaBetaREq (.all v A) (.all z (substFormula A v (.var z))) := by
    rw [Conversion.subst_formula_fresh_var A v z hzA]
    exact .all_rename v z A hty (.inr hzA)
  have h := FormulaConversion.subst_formula_congr x hrename (.refl t)
  rw [substFormula.eq_def (.all z (substFormula A v (.var z))) x t] at h
  simpa only [beq_eq_false_iff_ne.mpr hzx, Bool.false_eq_true, if_false, hzt] using h

/-- Instantiating the same quantified formula before or after a source conversion agrees. -/
theorem subst_formula_all_equiv {A B : Formula} {v w : Var}
    (h : FormulaBetaREq (.all v A) (.all w B)) (t : Term) :
    FormulaBetaREq (substFormula A v t) (substFormula B w t) :=
  (FormulaConversion.all_inversion h).2 t

end BBS2002.V2


/- Local checked proof module: MrSubstitutionAll -/

namespace BBS2002.V2

theorem Realizer.SupportedBy.subst {τ : Option Ty} {r : Realizer τ} {P : Var → Prop}
    (hr : r.SupportedBy P) (x : Var) (t : Term)
    (ht : ∀ z ∈ freeVars t, P z) : (Realizer.subst r x t).SupportedBy P := by
  cases τ with
  | none => exact Realizer.supportedBy_none P
  | some ρ =>
      apply (Realizer.supportedBy_some ρ _ P).mpr
      intro z hz
      rcases Support.subst_term_support r x t z (mem_eraseDups_iff.mp hz) with
        ⟨hz, _⟩ | hz
      · exact (Realizer.supportedBy_some ρ r P).mp hr z (mem_eraseDups_of_mem' _ hz)
      · exact ht z (mem_eraseDups_of_mem' _ hz)

theorem mr_substitution_all (ν : Ty) (comp : CompTerm ν) (v : Var) (A : Formula)
    (hSmall : ∀ C, formulaSize C < formulaSize (.all v A) →
      MRCompatible ν comp C ∧ MRSubstitution ν comp C)
    (hCurrent : MRCompatible ν comp (.all v A)) :
    MRSubstitution ν comp (.all v A) := by
  intro r x t hxC
  obtain ⟨z, hzTy, hz⟩ := FormulaConversion.exists_fresh_var
    ([x] ++ (allVarsFormula A ++ (allVarsFormula comp.body ++
      (r.toOption.toList.flatMap freeVars ++ freeVars t)))) v.ty
  simp only [List.mem_append, List.mem_singleton, not_or] at hz
  obtain ⟨hzx, hzA, hzC, hzRL, hzt⟩ := hz
  have hzAF : z ∉ freeVarsFormula A := fun h ↦ hzA (mem_freeVarsFormula_allVars h)
  have hzCF : z ∉ freeVarsFormula comp.body := fun h ↦ hzC (mem_freeVarsFormula_allVars h)
  have hzR : ∀ f ∈ r.toOption, z ∉ freeVars f := by
    intro f hf hzf
    exact hzRL (List.mem_flatMap.mpr ⟨f, Option.mem_toList.mpr hf, hzf⟩)
  have hztO : z ∉ freeVarOccurrences t := fun h ↦ hzt (mem_eraseDups_of_mem' _ h)
  let C := substFormula A v (.var z)
  let D := substFormula C x t
  let F := substFormula (.all v A) x t
  let a := Realizer.applyAll ν v A r (.var z)
  let b : Realizer (tau ν D) :=
    Realizer.cast (tau_substFormula ν C x t).symm (Realizer.subst a x t)
  let rs : Realizer (tau ν F) :=
    Realizer.cast (tau_substFormula ν (.all v A) x t).symm (Realizer.subst r x t)
  have hNorm : FormulaBetaREq F (.all z D) :=
    subst_formula_all_fresh A v z x t hzTy.symm hzA hzx hztO
  let s : Realizer (tau ν (.all z D)) := Realizer.cast (tau_formulaBetaREq ν hNorm) rs
  have hSopt : s.toOption = r.toOption.map (fun f ↦ substTerm f x t) :=
    (Realizer.toOption_cast _ _).trans
      ((Realizer.toOption_cast _ _).trans (Realizer.subst_toOption r x t))
  have hBopt : b.toOption =
      (r.toOption.map (fun f ↦ Term.app f (.var z))).map (fun f ↦ substTerm f x t) :=
    (Realizer.toOption_cast _ _).trans
      ((Realizer.subst_toOption a x t).trans
        (congrArg (fun q ↦ q.map (fun f ↦ substTerm f x t))
          (Realizer.applyAll_toOption ν v A r (.var z))))
  have hrP : r.SupportedBy (fun w ↦ w ≠ z) := by
    intro f hf w hw heq
    subst w
    exact hzR f hf hw
  have htP : ∀ w ∈ freeVars t, w ≠ z := by
    intro w hw heq
    subst w
    exact hzt hw
  have hsP : s.SupportedBy (fun w ↦ w ≠ z) := ((hrP.subst x t htP).cast _).cast _
  have hzS : ∀ f ∈ s.toOption, z ∉ freeVars f :=
    fun f hf hzf ↦ hsP f hf z hzf rfl
  have hSmallF : ∀ E, formulaSize E < formulaSize F →
      MRCompatible ν comp E ∧ MRSubstitution ν comp E := by
    intro E hE
    apply hSmall E
    simpa only [F, formulaSize_substFormula] using hE
  have hSmallD : ∀ E, formulaSize E < formulaSize (.all z D) →
      MRCompatible ν comp E ∧ MRSubstitution ν comp E := by
    intro E hE
    apply hSmall E
    simpa only [D, C, formulaSize, formulaSize_substFormula] using hE
  have hNormMR : FormulaBetaREq (mrFormula ν comp F rs)
      (mrFormula ν comp (.all z D) s) := by
    apply mr_congruence_step ν comp F hSmallF (.all z D) hNorm
    rw [show s.toOption = rs.toOption from Realizer.toOption_cast _ _]
    exact Realizer.toOption_rel_refl rs
  have hRightCanon := mr_all_fresh ν comp z D hSmallD s z rfl
    (not_mem_freeVarsFormula_all z D) hzS (.inr hzCF)
  have hRightBody :
      mrFormula ν comp (substFormula D z (.var z)) (Realizer.applyAll ν z D s (.var z)) =
        mrFormula ν comp D b := by
    apply mrFormula_source_eq ν comp (substFormula_var_self D z)
    rw [Realizer.applyAll_toOption, hSopt, hBopt]
    cases r.toOption <;>
      simp only [Option.map_none, Option.map_some, substTerm,
        beq_eq_false_iff_ne.mpr hzx, Bool.false_eq_true, ↓reduceIte]
  have hRight : FormulaBetaREq (mrFormula ν comp F rs) (.all z (mrFormula ν comp D b)) := by
    rw [hRightBody] at hRightCanon
    exact hNormMR.trans hRightCanon
  have hLeftCanon := mr_all_fresh ν comp v A hSmall r z hzTy
    (fun h ↦ hzAF (List.mem_filter.mp h).1) hzR (.inr hzCF)
  have hLeft := FormulaConversion.subst_formula_congr x hLeftCanon (.refl t)
  have hSubAll :
      substFormula (.all z (mrFormula ν comp C a)) x t =
        .all z (substFormula (mrFormula ν comp C a) x t) := by
    rw [substFormula.eq_def]
    simp only [beq_eq_false_iff_ne.mpr hzx, Bool.false_eq_true, ↓reduceIte, hztO]
  rw [hSubAll] at hLeft
  have hBody := (hSmall C (by
    simp only [C, formulaSize_substFormula, formulaSize]
    omega)).2 a x t hxC
  exact hLeft.trans ((FormulaBetaREq.all z hBody).trans hRight.symm)

end BBS2002.V2


/- Local checked proof module: MrSubstitutionStep -/

namespace BBS2002.V2

private theorem formula_transport {A B C D : Formula}
    (hA : A = C) (hB : B = D) (h : FormulaBetaREq C D) : FormulaBetaREq A B := by
  cases hA
  cases hB
  exact h

theorem exists_fresh_parameters (fs : List Formula) (rs : List (Option Term))
    (ts : List Term) (vs : List Var) (ρ : Ty) :
    ∃ z : Var, z.ty = ρ ∧
      (∀ A ∈ fs, z ∉ freeVarsFormula A) ∧
      (∀ r ∈ rs, ∀ t ∈ r, z ∉ freeVars t) ∧
      (∀ t ∈ ts, z ∉ freeVars t) ∧ z ∉ vs := by
  let vars := fs.flatMap freeVarsFormula ++ (rs.flatMap Option.toList).flatMap freeVars ++
    ts.flatMap freeVars ++ vs
  obtain ⟨z, hzTy, hz⟩ := FormulaConversion.exists_fresh_var vars ρ
  refine ⟨z, hzTy, ?_, ?_, ?_, ?_⟩
  · intro A hA hzA
    apply hz
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_flatMap.mpr ⟨A, hA, hzA⟩)))
  · intro r hr t ht hzt
    apply hz
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨t, List.mem_flatMap.mpr ⟨r, hr, ?_⟩, hzt⟩
    cases r with
    | none => cases ht
    | some q => exact List.mem_singleton.mpr (Option.some.inj (Option.mem_def.mp ht)).symm
  · intro t ht hzt
    exact hz (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ht, hzt⟩)))
  · intro hzv
    exact hz (List.mem_append_right _ hzv)

theorem applyImp_subst_toOption (ν : Ty) (A B C D : Formula)
    (r : Realizer (tau ν (.imp A B))) (a : Realizer (tau ν A))
    (r' : Realizer (tau ν (.imp C D))) (a' : Realizer (tau ν C))
    (x : Var) (t : Term)
    (hr : r'.toOption = (Realizer.subst r x t).toOption)
    (ha : a'.toOption = (Realizer.subst a x t).toOption) :
    (Realizer.applyImp ν C D r' a').toOption =
      (Realizer.subst (Realizer.applyImp ν A B r a) x t).toOption := by
  rw [Realizer.applyImp_toOption, hr, ha, Realizer.subst_toOption,
    Realizer.subst_toOption, Realizer.subst_toOption, Realizer.applyImp_toOption]
  cases r.toOption <;> cases a.toOption <;> simp only [Option.map_none, Option.map_some, substTerm]

theorem mr_substitution_step (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (hSmall : ∀ C, formulaSize C < formulaSize A → MRCompatible ν comp C ∧ MRSubstitution ν comp C)
    (hCurrent : MRCompatible ν comp A) : MRSubstitution ν comp A := by
  intro r x t hxC
  match A with
  | .bot =>
      exact formula_transport
        ((congrArg (fun F ↦ substFormula F x t) (mrFormula.eq_def ν comp .bot r)).trans
          (substFormula_bot x t))
        ((mrFormula_source_eq ν comp (substFormula_bot x t) _ ()
          (by rw [Realizer.toOption_cast, Realizer.subst_toOption]; rfl)).trans
          (mrFormula.eq_def ν comp .bot ())) .bot
  | .varX =>
      exact formula_transport
        (congrArg (fun F ↦ substFormula F x t) (mrFormula.eq_def ν comp .varX r))
        ((mrFormula_source_eq ν comp (substFormula_varX x t) _ (substTerm r x t)
          (by rw [Realizer.toOption_cast, Realizer.subst_toOption]; rfl)).trans
          (mrFormula.eq_def ν comp .varX (substTerm r x t)))
        (FormulaConversion.subst_formula_comprehension comp.body comp.var x r t hxC)
  | .atom a =>
      exact formula_transport
        ((congrArg (fun F ↦ substFormula F x t) (mrFormula.eq_def ν comp (.atom a) r)).trans
          (substFormula_atom a x t))
        ((mrFormula_source_eq ν comp (substFormula_atom a x t) _ ()
          (by rw [Realizer.toOption_cast, Realizer.subst_toOption]; rfl)).trans
          (mrFormula.eq_def ν comp (.atom (substTerm a x t)) ())) (.refl _)
  | .imp A B =>
      have hA := hSmall A (by simp [formulaSize]; omega)
      have hB := hSmall B (by simp [formulaSize]; omega)
      let rs : Realizer (tau ν (.imp (substFormula A x t) (substFormula B x t))) :=
        Realizer.cast (by simp only [tau, tau_substFormula]) (Realizer.subst r x t)
      have hRS : rs.toOption = (Realizer.subst r x t).toOption := Realizer.toOption_cast _ _
      have hTarget := mrFormula_source_eq ν comp (substFormula_imp A B x t)
        (Realizer.cast (tau_substFormula ν (.imp A B) x t).symm (Realizer.subst r x t)) rs
        ((Realizer.toOption_cast _ _).trans hRS.symm)
      cases hτA : tau ν A with
      | none =>
          let ar : Realizer (tau ν A) := Realizer.cast hτA.symm ()
          let ar' : Realizer (tau ν (substFormula A x t)) :=
            Realizer.cast (tau_substFormula ν A x t).symm (Realizer.subst ar x t)
          refine formula_transport
            ((congrArg (fun F ↦ substFormula F x t) (mrFormula_imp_none ν comp A B hτA r ar)).trans
              (substFormula_imp _ _ x t))
            (hTarget.trans (mrFormula_imp_none ν comp _ _
              ((tau_substFormula ν A x t).trans hτA) rs ar')) ?_
          refine .imp (hA.2 ar x t hxC) ?_
          exact formula_transport rfl
            (mrFormula_source_eq ν comp rfl _ _
              ((applyImp_subst_toOption ν A B _ _ r ar rs ar' x t hRS
                (Realizer.toOption_cast _ _)).trans (Realizer.toOption_cast _ _).symm))
            (hB.2 (Realizer.applyImp ν A B r ar) x t hxC)
      | some ρ =>
          have hAS := hSmall (substFormula A x t) (by
            simp only [formulaSize_substFormula, formulaSize]; omega)
          have hBS := hSmall (substFormula B x t) (by
            simp only [formulaSize_substFormula, formulaSize]; omega)
          obtain ⟨z, hzTy, hzF, hzR, hzT, hzX⟩ := exists_fresh_parameters
            [A, B, substFormula A x t, substFormula B x t, comp.body]
            [r.toOption, rs.toOption] [t] [x] ρ
          have hzx : z ≠ x := by simpa only [List.mem_singleton] using hzX
          have hzt : z ∉ freeVarOccurrences t := fun hz ↦
            hzT t (by simp) (mem_eraseDups_of_mem' _ hz)
          have hzComp : z = comp.var ∨ z ∉ freeVarsFormula comp.body :=
            .inr (hzF comp.body (by simp))
          let ar : Realizer (tau ν A) := Realizer.cast hτA.symm (Term.var z)
          let ar' : Realizer (tau ν (substFormula A x t)) :=
            Realizer.cast ((tau_substFormula ν A x t).trans hτA).symm (Term.var z)
          have hAR : ar'.toOption = (Realizer.subst ar x t).toOption := by
            have ha : ar.toOption = some (.var z) := Realizer.toOption_cast _ _
            have ha' : ar'.toOption = some (.var z) := Realizer.toOption_cast _ _
            rw [ha', Realizer.subst_toOption, ha]
            simp only [Option.map_some, substTerm, beq_iff_eq, hzx, ↓reduceIte]
          have hLeft := mr_imp_fresh ν comp A B hA hB ρ hτA r z hzTy
            (hzF A (by simp)) (hzF B (by simp))
            (hzR r.toOption (by simp)) hzComp
          have hRight := mr_imp_fresh ν comp (substFormula A x t) (substFormula B x t)
            hAS hBS ρ ((tau_substFormula ν A x t).trans hτA) rs z hzTy
            (hzF _ (by simp)) (hzF _ (by simp))
            (hzR rs.toOption (by simp)) hzComp
          refine (FormulaConversion.subst_formula_congr x hLeft (.refl t)).trans ?_
          refine FormulaBetaREq.trans ?_ (formula_transport hTarget rfl hRight).symm
          have hBinder : substFormula
              (.all z (.imp (mrFormula ν comp A ar)
                (mrFormula ν comp B (Realizer.applyImp ν A B r ar)))) x t =
              .all z (.imp (substFormula (mrFormula ν comp A ar) x t)
                (substFormula (mrFormula ν comp B (Realizer.applyImp ν A B r ar)) x t)) := by
            rw [substFormula.eq_def]
            simp only [beq_iff_eq, hzx, hzt, ↓reduceIte, substFormula_imp]
          refine formula_transport hBinder rfl (.all z (.imp ?_ ?_))
          · exact formula_transport rfl
              (mrFormula_source_eq ν comp rfl ar' _
                (hAR.trans (Realizer.toOption_cast _ _).symm))
              (hA.2 ar x t hxC)
          · exact formula_transport rfl
              (mrFormula_source_eq ν comp rfl _ _
                ((applyImp_subst_toOption ν A B _ _ r ar rs ar' x t hRS hAR).trans
                  (Realizer.toOption_cast _ _).symm))
              (hB.2 (Realizer.applyImp ν A B r ar) x t hxC)
  | .all v A =>
      exact mr_substitution_all ν comp v A hSmall hCurrent r x t hxC

end BBS2002.V2


/- Local checked proof module: MrTransportLaws -/

namespace BBS2002.V2

theorem mrFormula_transport_laws (ν : Ty) (comp : CompTerm ν) (A : Formula) :
    MRCompatible ν comp A ∧ MRSubstitution ν comp A := by
  suffices ∀ n, ∀ A : Formula, formulaSize A = n →
      MRCompatible ν comp A ∧ MRSubstitution ν comp A from this (formulaSize A) A rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro A hEq
      have hSmall : ∀ C, formulaSize C < formulaSize A →
          MRCompatible ν comp C ∧ MRSubstitution ν comp C := by
        intro C hC
        exact ih (formulaSize C) (hEq ▸ hC) C rfl
      have hc := mr_congruence_step ν comp A hSmall
      exact ⟨hc, mr_substitution_step ν comp A hSmall hc⟩

theorem mrFormula_compatible (ν : Ty) (comp : CompTerm ν) (A : Formula) :
    MRCompatible ν comp A :=
  (mrFormula_transport_laws ν comp A).1

theorem mrFormula_substitution (ν : Ty) (comp : CompTerm ν) (A : Formula) :
    MRSubstitution ν comp A :=
  (mrFormula_transport_laws ν comp A).2

theorem mrFormula_congr (ν : Ty) (comp : CompTerm ν) (A B : Formula)
    (r : Realizer (tau ν A)) (s : Realizer (tau ν B))
    (hAB : FormulaBetaREq A B) (hrs : Option.Rel BetaREq r.toOption s.toOption) :
    FormulaBetaREq (mrFormula ν comp A r) (mrFormula ν comp B s) :=
  mrFormula_compatible ν comp A B hAB r s hrs

theorem mrFormula_subst (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (r : Realizer (tau ν A)) (x : Var) (t : Term)
    (hxC : x = comp.var ∨ x ∉ freeVarsFormula comp.body) :
    FormulaBetaREq (substFormula (mrFormula ν comp A r) x t)
      (mrFormula ν comp (substFormula A x t)
        (Realizer.cast (tau_substFormula ν A x t).symm (Realizer.subst r x t))) :=
  mrFormula_substitution ν comp A r x t hxC

end BBS2002.V2


/- Local checked proof module: MrLogic -/

namespace BBS2002.V2.MrLogic

theorem mr_allowed (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (r : Realizer (tau ν A)) (hA : FormulaWellTyped A) (hr : r.Typed) :
    SysConfig.Z.allowsFormula (mrFormula ν comp A r) :=
  ⟨mrFormula_wellTyped ν comp A r hA hr, .inr (mrFormula_isL ν comp A r)⟩

theorem all_imp_convert (x : Var) (t : Term) (P Q S T : Formula)
    (ht : HasType t x.ty)
    (hP : SysConfig.Z.allowsFormula P) (hQ : SysConfig.Z.allowsFormula Q)
    (hS : SysConfig.Z.allowsFormula S) (hT : SysConfig.Z.allowsFormula T)
    (hPS : FormulaBetaREq (substFormula P x t) S)
    (hQT : FormulaBetaREq (substFormula Q x t) T) :
    Provable SysConfig.Z (.imp (.all x (.imp P Q)) (.imp S T)) := by
  apply Provable.conv (Provable.imp_all_elim x t ht (hP.imp hQ))
    (((hP.imp hQ).all x).imp (hS.imp hT))
  exact .imp (.refl _) (by simpa only [substFormula] using FormulaBetaREq.imp hPS hQT)

theorem toOption_none {τ : Option Ty} (r : Realizer τ) (h : τ = none) :
    r.toOption = none := by
  cases h
  rfl

theorem toOption_some {τ : Option Ty} {ρ : Ty} (r : Realizer τ) (h : τ = some ρ) :
    r.toOption = some (Realizer.cast h r) := by
  cases h
  rfl

theorem mr_subst_replace (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (hc : MRCompatible ν comp A) (hs : MRSubstitution ν comp A)
    (r s : Realizer (tau ν A)) (x : Var) (t : Term)
    (hxA : x ∉ allVarsFormula A)
    (hxC : x = comp.var ∨ x ∉ freeVarsFormula comp.body)
    (hrs : Option.Rel BetaREq (Realizer.subst r x t).toOption s.toOption) :
    FormulaBetaREq (substFormula (mrFormula ν comp A r) x t) (mrFormula ν comp A s) :=
  (mr_subst_fresh_source ν comp A hc hs r x t
    (fun h => hxA (mem_freeVarsFormula_allVars h)) hxC).trans (hc A (.refl A) _ s hrs)

theorem mr_imp_elim (ν : Ty) (comp : CompTerm ν)
    (hc : ∀ A, MRCompatible ν comp A) (hs : ∀ A, MRSubstitution ν comp A)
    (A B : Formula) (r : Realizer (tau ν (.imp A B))) (a : Realizer (tau ν A))
    (hA : FormulaWellTyped A) (hB : FormulaWellTyped B) (hr : r.Typed) (ha : a.Typed) :
    Provable SysConfig.Z
      (.imp (mrFormula ν comp (.imp A B) r)
        (.imp (mrFormula ν comp A a) (mrFormula ν comp B (Realizer.applyImp ν A B r a)))) := by
  have hInput := mr_allowed ν comp (.imp A B) r (.imp hA hB) hr
  have hAnte := mr_allowed ν comp A a hA ha
  have hCons := mr_allowed ν comp B (Realizer.applyImp ν A B r a) hB
    (Realizer.applyImp_typed ν A B r a hr ha)
  rw [mrFormula.eq_def ν comp (.imp A B) r]
  dsimp only
  split
  · rename_i hτA hτB
    let ar : Realizer (tau ν A) := Realizer.cast hτA.symm ()
    let br : Realizer (tau ν B) := Realizer.cast hτB.symm ()
    have eA := hc A A (.refl A) ar a (by
      rw [toOption_none ar hτA, toOption_none a hτA]
      exact .none)
    have eB := hc B B (.refl B) br (Realizer.applyImp ν A B r a) (by
      rw [toOption_none br hτB, toOption_none _ hτB]
      exact .none)
    have hP := mr_allowed ν comp A ar hA ((Realizer.typed_cast _ _).mpr True.intro)
    have hQ := mr_allowed ν comp B br hB ((Realizer.typed_cast _ _).mpr True.intro)
    exact Provable.conv (Provable.id (hAnte.imp hCons))
      ((hP.imp hQ).imp (hAnte.imp hCons)) (.imp (.imp eA.symm eB.symm) (.refl _))
  · rename_i σ hτA hτB
    let ar : Realizer (tau ν A) := Realizer.cast hτA.symm ()
    have hτ : tau ν (.imp A B) = tau ν B := by simp only [tau, hτA]
    let br : Realizer (tau ν B) := Realizer.cast hτ r
    have hOut : (Realizer.applyImp ν A B r a).toOption = r.toOption := by
      rw [Realizer.applyImp_toOption, toOption_none a hτA]
      cases r.toOption <;> rfl
    have eA := hc A A (.refl A) ar a (by
      rw [toOption_none ar hτA, toOption_none a hτA]
      exact .none)
    have eB := hc B B (.refl B) br (Realizer.applyImp ν A B r a) (by
      rw [show br.toOption = r.toOption from Realizer.toOption_cast hτ r, hOut]
      exact Realizer.toOption_rel_refl r)
    have hP := mr_allowed ν comp A ar hA ((Realizer.typed_cast _ _).mpr True.intro)
    have hQ := mr_allowed ν comp B br hB ((Realizer.typed_cast _ _).mpr hr)
    exact Provable.conv (Provable.id (hAnte.imp hCons))
      ((hP.imp hQ).imp (hAnte.imp hCons)) (.imp (.imp eA.symm eB.symm) (.refl _))
  · rename_i ρ hτA hτB
    let z := freshVar comp none A B ρ
    let t : Term := Realizer.cast hτA a
    let ar : Realizer (tau ν A) := Realizer.cast hτA.symm (.var z)
    let br : Realizer (tau ν B) := Realizer.cast hτB.symm ()
    have ht : HasType t z.ty := (Realizer.typed_cast hτA a).mpr ha
    have har : ar.Typed := (Realizer.typed_cast hτA.symm (.var z)).mpr (HasType.var z)
    have hbr : br.Typed := (Realizer.typed_cast hτB.symm ()).mpr True.intro
    have hAr : ar.toOption = some (.var z) :=
      Realizer.toOption_cast (τ := some ρ) hτA.symm (.var z)
    have hVar : substTerm (.var z) z t = t := by simp [substTerm]
    have eA := mr_subst_replace ν comp A (hc A) (hs A) ar a z t
      (freshVar_not_mem_allVars_left comp none A B ρ)
      (.inr (freshVar_not_free_compBody comp none A B ρ)) (by
        rw [Realizer.subst_toOption, hAr, Option.map_some, hVar, toOption_some a hτA]
        exact .some (.refl t))
    have eB := mr_subst_replace ν comp B (hc B) (hs B) br
      (Realizer.applyImp ν A B r a) z t
      (freshVar_not_mem_allVars_right comp none A B ρ)
      (.inr (freshVar_not_free_compBody comp none A B ρ)) (by
        rw [Realizer.subst_toOption, toOption_none br hτB, Option.map_none, toOption_none _ hτB]
        exact .none)
    exact all_imp_convert z t _ _ _ _ ht (mr_allowed ν comp A ar hA har)
      (mr_allowed ν comp B br hB hbr) hAnte hCons eA eB
  · rename_i ρ σ hτA hτB
    have hτR : tau ν (.imp A B) = some (.arr ρ σ) := by simp only [tau, hτA, hτB]
    let f : Term := Realizer.cast hτR r
    let z := freshVar comp (some f) A B ρ
    let t : Term := Realizer.cast hτA a
    let ar : Realizer (tau ν A) := Realizer.cast hτA.symm (.var z)
    let br : Realizer (tau ν B) := Realizer.cast hτB.symm (.app f (.var z))
    have hf : HasType f (.arr ρ σ) := (Realizer.typed_cast hτR r).mpr hr
    have ht : HasType t z.ty := (Realizer.typed_cast hτA a).mpr ha
    have har : ar.Typed := (Realizer.typed_cast hτA.symm (.var z)).mpr (HasType.var z)
    have hbr : br.Typed := (Realizer.typed_cast hτB.symm (.app f (.var z))).mpr
      (.app hf (HasType.var z))
    have hAr : ar.toOption = some (.var z) :=
      Realizer.toOption_cast (τ := some ρ) hτA.symm (.var z)
    have hBr : br.toOption = some (.app f (.var z)) :=
      Realizer.toOption_cast (τ := some σ) hτB.symm (.app f (.var z))
    have hVar : substTerm (.var z) z t = t := by simp [substTerm]
    have eA := mr_subst_replace ν comp A (hc A) (hs A) ar a z t
      (freshVar_not_mem_allVars_left comp (some f) A B ρ)
      (.inr (freshVar_not_free_compBody comp (some f) A B ρ)) (by
        rw [Realizer.subst_toOption, hAr, Option.map_some, hVar, toOption_some a hτA]
        exact .some (.refl t))
    have hFn : z ∉ freeVarOccurrences f := fun hz =>
      freshVar_not_mem_realizer comp f A B ρ (mem_freeVarOccurrences_of_mem_allVars hz)
    have hApp : BetaREq (substTerm (.app f (.var z)) z t) (.app f t) := by
      rw [substTerm.eq_def (.app f (.var z)) z t]
      dsimp only
      rw [hVar]
      exact .app (.of_alpha (substTerm_alphaEq_of_not_free f z t hFn)) (.refl t)
    have eB := mr_subst_replace ν comp B (hc B) (hs B) br
      (Realizer.applyImp ν A B r a) z t
      (freshVar_not_mem_allVars_right comp (some f) A B ρ)
      (.inr (freshVar_not_free_compBody comp (some f) A B ρ)) (by
        rw [Realizer.subst_toOption, hBr, Option.map_some, Realizer.applyImp_toOption,
          toOption_some r hτR, toOption_some a hτA]
        exact .some hApp)
    exact all_imp_convert z t _ _ _ _ ht (mr_allowed ν comp A ar hA har)
      (mr_allowed ν comp B br hB hbr) hAnte hCons eA eB

end BBS2002.V2.MrLogic


/- Local checked proof module: Hygiene -/

namespace BBS2002.V2.Hygiene

/-- Relabel an assumption without changing its formula. -/
def relabelVar (f : AssumpVar → Nat) (u : AssumpVar) : AssumpVar := ⟨f u, u.formula⟩

/-- Uniformly relabel assumption variables throughout a proof term. -/
def relabel (f : AssumpVar → Nat) : ProofTerm → ProofTerm
  | .assump u => .assump (relabelVar f u)
  | .indNat x A => .indNat x A
  | .indBool x A => .indBool x A
  | .axTrue => .axTrue
  | .axFalse A => .axFalse A
  | .efq A => .efq A
  | .lamAssump u M => .lamAssump (relabelVar f u) (relabel f M)
  | .appAssump M N => .appAssump (relabel f M) (relabel f N)
  | .lamTerm x M => .lamTerm x (relabel f M)
  | .appTerm M t => .appTerm (relabel f M) t

/-- Relabeling creates no new free assumptions. Identifying equal-formula labels may discharge
additional occurrences, so this direction does not require injectivity. -/
theorem freeAssumpVars_relabel {f : AssumpVar → Nat} {M : ProofTerm} {v : AssumpVar}
    (hv : v ∈ freeAssumpVars (relabel f M)) :
    ∃ u ∈ freeAssumpVars M, v = relabelVar f u := by
  induction M generalizing v with
  | assump u => exact ⟨u, List.mem_singleton_self _, by simpa [relabel, freeAssumpVars] using hv⟩
  | indNat | indBool | axTrue | axFalse | efq => cases hv
  | lamAssump u M ih =>
      obtain ⟨hv, hne⟩ := List.mem_filter.mp hv
      obtain ⟨w, hw, hEq⟩ := ih hv
      refine ⟨w, List.mem_filter.mpr ⟨hw, ?_⟩, hEq⟩
      simp only [bne_iff_ne] at hne ⊢
      exact fun hwu ↦ hne (hEq.trans (congrArg (relabelVar f) hwu))
  | appAssump M N ihM ihN =>
      simp only [relabel, freeAssumpVars, List.mem_eraseDups, List.mem_append] at hv ⊢
      rcases hv with hv | hv
      · obtain ⟨u, hu, hEq⟩ := ihM hv
        exact ⟨u, Or.inl hu, hEq⟩
      · obtain ⟨u, hu, hEq⟩ := ihN hv
        exact ⟨u, Or.inr hu, hEq⟩
  | lamTerm x M ih => exact ih hv
  | appTerm M t ih => exact ih hv

theorem derivable_relabel {sys : SysConfig} {M : ProofTerm} {B : Formula}
    (h : Derivable sys M B) (f : AssumpVar → Nat) : Derivable sys (relabel f M) B := by
  induction h with
  | assump u hA => exact .assump (relabelVar f u) hA
  | indNat n A hn hA => exact .indNat n A hn hA
  | indBool p A hp hA => exact .indBool p A hp hA
  | axTrue => exact .axTrue
  | axFalse A hA => exact .axFalse A hA
  | efq A hsys hA => exact .efq A hsys hA
  | lamAssump u hA _ ih => exact .lamAssump (relabelVar f u) hA ih
  | appAssump _ _ ihM ihN => exact .appAssump ihM ihN
  | lamTerm x hfree _ ih =>
      refine .lamTerm x ?_ ih
      intro v hv
      obtain ⟨u, hu, rfl⟩ := freeAssumpVars_relabel hv
      exact hfree u hu
  | appTerm t ht _ ih => exact .appTerm t ht ih
  | conv _ hB hEq ih => exact .conv ih hB hEq

theorem closed_relabel {f : AssumpVar → Nat} {M : ProofTerm}
    (h : freeAssumpVars M = []) : freeAssumpVars (relabel f M) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro v hv
  obtain ⟨u, hu, _⟩ := freeAssumpVars_relabel hv
  simp [h] at hu

theorem allAssumpVars_relabel (f : AssumpVar → Nat) (M : ProofTerm) :
    allAssumpVars (relabel f M) = (allAssumpVars M).map (relabelVar f) := by
  induction M <;> simp_all [relabel, allAssumpVars, List.map_append]

theorem allVarsProof_relabel (f : AssumpVar → Nat) (M : ProofTerm) :
    allVarsProof (relabel f M) = allVarsProof M := by
  induction M <;> simp_all [relabel, relabelVar, allVarsProof]

/-- Give each full assumption label in a proof a distinct ID above `base`. -/
def freshLabel (base : Nat) (M : ProofTerm) (u : AssumpVar) : Nat :=
  base + (allAssumpVars M).idxOf u

def freshen (base : Nat) (M : ProofTerm) : ProofTerm := relabel (freshLabel base M) M

theorem freshen_ids_ge {base : Nat} {M : ProofTerm} {u : AssumpVar}
    (hu : u ∈ allAssumpVars (freshen base M)) : base ≤ u.id := by
  rw [freshen, allAssumpVars_relabel] at hu
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hu
  exact Nat.le_add_right base _

theorem freshen_consistent {base : Nat} {M : ProofTerm} {u v : AssumpVar}
    (hu : u ∈ allAssumpVars (freshen base M))
    (hv : v ∈ allAssumpVars (freshen base M))
    (hID : u.id = v.id) : u.formula = v.formula := by
  rw [freshen, allAssumpVars_relabel] at hu hv
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
  have hIndex : (allAssumpVars M).idxOf a = (allAssumpVars M).idxOf b :=
    Nat.add_left_cancel hID
  have hGet : (allAssumpVars M)[(allAssumpVars M).idxOf b]'(List.idxOf_lt_length_of_mem hb) = a := by
    simpa only [hIndex] using (List.getElem_idxOf (List.idxOf_lt_length_of_mem ha))
  change a.formula = b.formula
  exact congrArg AssumpVar.formula
    (hGet.symm.trans (List.getElem_idxOf (List.idxOf_lt_length_of_mem hb)))

def maxObjectId (M : ProofTerm) : Nat :=
  (allVarsProof M).foldr (fun x n ↦ max x.id n) 0

theorem id_le_foldr_max {xs : List Var} {x : Var} (hx : x ∈ xs) :
    x.id ≤ xs.foldr (fun y n ↦ max y.id n) 0 := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

/-- Freshening suffices for the extraction naming convention, independently of comp. -/
theorem freshen_admissible (ν : Ty) (dummy : Term) (M : ProofTerm)
    (hDummyTy : HasType dummy ν) (hDummyClosed : IsClosedTerm dummy) :
    AdmissibleForExtraction ν dummy (freshen (maxObjectId M + 1) M) := by
  refine ⟨hDummyTy, hDummyClosed, ?_, ?_⟩
  · intro u hu x hx
    rw [freshen, allVarsProof_relabel] at hx
    have huID := freshen_ids_ge hu
    have hxID : x.id ≤ maxObjectId M := id_le_foldr_max hx
    omega
  · intro u hu v hv hID
    exact freshen_consistent hu hv hID

/-- Any closed-assumption derivation can be put in the extraction naming convention without
changing its formula. This is an explicit syntactic relabeling, not an extra soundness premise. -/
theorem exists_admissible_proof {sys : SysConfig} {M : ProofTerm} {B : Formula}
    (hM : Derivable sys M B) (hClosed : freeAssumpVars M = [])
    (ν : Ty) (dummy : Term) (hDummyTy : HasType dummy ν)
    (hDummyClosed : IsClosedTerm dummy) :
    ∃ N : ProofTerm, Derivable sys N B ∧ freeAssumpVars N = [] ∧
      AdmissibleForExtraction ν dummy N :=
  ⟨freshen (maxObjectId M + 1) M,
    derivable_relabel hM _, closed_relabel hClosed,
    freshen_admissible ν dummy M hDummyTy hDummyClosed⟩

end BBS2002.V2.Hygiene


/- Local checked proof module: Support -/

namespace BBS2002.V2.Support

/-- Object variables which can occur freely in raw extraction, before accounting for
the realizer variables of free assumptions. Formula annotations contribute no terms. -/
def objectSupport : ProofTerm → List Var
  | .assump _ | .indNat _ _ | .indBool _ _ | .axTrue | .axFalse _ | .efq _ => []
  | .lamAssump _ M => objectSupport M
  | .appAssump M N => objectSupport M ++ objectSupport N
  | .lamTerm x M => (objectSupport M).filter (· != x)
  | .appTerm M t => objectSupport M ++ freeVars t

@[simp] theorem mem_freeVars_iff {x : Var} {t : Term} :
    x ∈ freeVars t ↔ x ∈ freeVarOccurrences t := by
  simp only [freeVars, List.mem_eraseDups]

@[simp] theorem mem_freeVars_lam {x y : Var} {t : Term} :
    x ∈ freeVars (.lam y t) ↔ x ∈ freeVars t ∧ x ≠ y := by
  simp only [mem_freeVars_iff, freeVarOccurrences, List.mem_filter, bne_iff_ne]

@[simp] theorem mem_freeVars_app {x : Var} {r s : Term} :
    x ∈ freeVars (.app r s) ↔ x ∈ freeVars r ∨ x ∈ freeVars s := by
  simp only [mem_freeVars_iff, freeVarOccurrences, List.mem_append]

@[simp] theorem defaultTerm_freeVars (ρ : Ty) : freeVars (defaultTerm ρ) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  induction ρ with
  | iota | bool => cases hx
  | arr ρ σ ihρ ihσ => exact ihσ (mem_freeVars_lam.mp hx).1

theorem defaultTerm_typed (ρ : Ty) : HasType (defaultTerm ρ) ρ := by
  induction ρ with
  | iota => exact .const .zero
  | bool => exact .const .falseConst
  | arr ρ σ _ ih => exact .lam ⟨0, ρ⟩ ih

theorem efqTerm_closed (ν : Ty) (dummy : Term) (ρ : Ty)
    (hDummy : IsClosedTerm dummy) : freeVars (efqTerm ν dummy ρ) = [] := by
  simp only [efqTerm]
  split
  · exact hDummy
  · exact defaultTerm_freeVars ρ

/-- Every free variable in the structural extracted term comes from an object-term
argument or from a free assumption label. This is only a support bound. -/
theorem extractRaw_support (ν : Ty) (dummy : Term) (hDummy : IsClosedTerm dummy)
    (M : ProofTerm) {t : Term} (ht : extractRaw ν dummy M = some t)
    {x : Var} (hx : x ∈ freeVars t) :
    x ∈ objectSupport M ∨
      ∃ u ∈ freeAssumpVars M, assumpRealizerVar ν u = some x := by
  induction M generalizing t x with
  | assump u =>
      simp only [extractRaw, assumpRealizerTerm] at ht
      cases hR : assumpRealizerVar ν u with
      | none => simp [hR] at ht
      | some y =>
          simp only [hR, Option.map_some, Option.some.injEq] at ht
          subst t
          have hxy : x = y := by simpa [freeVars, freeVarOccurrences] using hx
          subst x
          exact Or.inr ⟨u, List.mem_singleton_self _, hR⟩
  | indNat n A | indBool n A =>
      simp only [extractRaw] at ht
      cases hτ : tau ν A with
      | none => simp [hτ] at ht
      | some ρ =>
          simp only [hτ, Option.map_some, Option.some.injEq] at ht
          subst t
          cases hx
  | axTrue => cases ht
  | axFalse A | efq A =>
      simp only [extractRaw] at ht
      cases hτ : tau ν A with
      | none => simp [hτ] at ht
      | some ρ =>
          simp only [hτ, Option.map_some, Option.some.injEq] at ht
          subst t
          rw [efqTerm_closed ν dummy ρ hDummy] at hx
          cases hx
  | lamAssump u M ih =>
      simp only [extractRaw] at ht
      cases hτ : tau ν u.formula with
      | none =>
          simp only [hτ] at ht
          rcases ih ht hx with hObj | ⟨v, hv, hV⟩
          · exact Or.inl hObj
          · refine Or.inr ⟨v, List.mem_filter.mpr ⟨hv, ?_⟩, hV⟩
            simp only [bne_iff_ne]
            intro hvu
            subst v
            simp [assumpRealizerVar, hτ] at hV
      | some ρ =>
          simp only [hτ] at ht
          cases hM : extractRaw ν dummy M with
          | none => simp [hM] at ht
          | some m =>
              simp only [hM, Option.map_some, Option.some.injEq] at ht
              subst t
              obtain ⟨hx, hne⟩ := mem_freeVars_lam.mp hx
              rcases ih hM hx with hObj | ⟨v, hv, hV⟩
              · exact Or.inl hObj
              · refine Or.inr ⟨v, List.mem_filter.mpr ⟨hv, ?_⟩, hV⟩
                simp only [bne_iff_ne]
                intro hvu
                subst v
                have hX : (⟨u.id, ρ⟩ : Var) = x := by
                  simpa [assumpRealizerVar, hτ] using hV
                exact hne hX.symm
  | appAssump M N ihM ihN =>
      simp only [extractRaw] at ht
      cases hM : extractRaw ν dummy M with
      | none => simp [hM] at ht
      | some m =>
          cases hN : extractRaw ν dummy N with
          | none =>
              simp only [hM, hN, Option.some.injEq] at ht
              subst t
              rcases ihM hM hx with hObj | ⟨u, hu, hU⟩
              · exact Or.inl (List.mem_append_left _ hObj)
              · exact Or.inr ⟨u, List.mem_eraseDups.mpr (List.mem_append_left _ hu), hU⟩
          | some n =>
              simp only [hM, hN, Option.some.injEq] at ht
              subst t
              rcases mem_freeVars_app.mp hx with hx | hx
              · rcases ihM hM hx with hObj | ⟨u, hu, hU⟩
                · exact Or.inl (List.mem_append_left _ hObj)
                · exact Or.inr ⟨u, List.mem_eraseDups.mpr (List.mem_append_left _ hu), hU⟩
              · rcases ihN hN hx with hObj | ⟨u, hu, hU⟩
                · exact Or.inl (List.mem_append_right _ hObj)
                · exact Or.inr ⟨u, List.mem_eraseDups.mpr (List.mem_append_right _ hu), hU⟩
  | lamTerm y M ih =>
      simp only [extractRaw] at ht
      cases hM : extractRaw ν dummy M with
      | none => simp [hM] at ht
      | some m =>
          simp only [hM, Option.map_some, Option.some.injEq] at ht
          subst t
          obtain ⟨hx, hne⟩ := mem_freeVars_lam.mp hx
          rcases ih hM hx with hObj | hAssump
          · exact Or.inl (List.mem_filter.mpr ⟨hObj, by simpa using hne⟩)
          · exact Or.inr hAssump
  | appTerm M s ih =>
      simp only [extractRaw] at ht
      cases hM : extractRaw ν dummy M with
      | none => simp [hM] at ht
      | some m =>
          simp only [hM, Option.map_some, Option.some.injEq] at ht
          subst t
          rcases mem_freeVars_app.mp hx with hx | hx
          · rcases ih hM hx with hObj | hAssump
            · exact Or.inl (List.mem_append_left _ hObj)
            · exact Or.inr hAssump
          · exact Or.inl (List.mem_append_right _ hx)

theorem extractProgram_support (ν : Ty) (dummy : Term) (hDummy : IsClosedTerm dummy)
    (M : ProofTerm) (B : Formula) {t : Term}
    (ht : extractProgram ν dummy M B = some t) {x : Var} (hx : x ∈ freeVars t) :
    x ∈ objectSupport M ∨
      ∃ u ∈ freeAssumpVars M, assumpRealizerVar ν u = some x := by
  cases hτ : tau ν B with
  | none => simp [extractProgram, hτ] at ht
  | some ρ => exact extractRaw_support ν dummy hDummy M (by simpa [extractProgram, hτ] using ht) hx

theorem objectSupport_relabel (f : AssumpVar → Nat) (M : ProofTerm) :
    objectSupport (Hygiene.relabel f M) = objectSupport M := by
  induction M <;> simp_all [Hygiene.relabel, objectSupport]

theorem not_mem_freeVarOccurrences_of_closed {t : Term} (h : IsClosedTerm t) (x : Var) :
    x ∉ freeVarOccurrences t := by
  intro hx
  have hx' : x ∈ freeVars t := mem_freeVars_iff.mpr hx
  rw [h] at hx'
  cases hx'

/-- Substituting a closed term for an absent variable is literal equality, since no
capture-avoidance renaming is needed. -/
theorem substTerm_eq_of_not_free_of_closed (r : Term) (x : Var) (t : Term)
    (hClosed : IsClosedTerm t) (hx : x ∉ freeVars r) : substTerm r x t = r := by
  induction r with
  | var y =>
      have hxy : y ≠ x := by
        intro h
        subst y
        exact hx (by simp [freeVars, freeVarOccurrences])
      simp [substTerm, hxy]
  | const c => simp only [substTerm]
  | lam y r ih =>
      by_cases hyx : y = x
      · simp [substTerm, hyx]
      · have hx' : x ∉ freeVars r := by
          intro hxr
          exact hx (mem_freeVars_lam.mpr ⟨hxr, Ne.symm hyx⟩)
        simpa only [substTerm, beq_iff_eq, hyx, ↓reduceIte,
          not_mem_freeVarOccurrences_of_closed hClosed y] using congrArg (Term.lam y) (ih hx')
  | app r s ihr ihs =>
      have hr : x ∉ freeVars r := fun h ↦ hx (mem_freeVars_app.mpr (Or.inl h))
      have hs : x ∉ freeVars s := fun h ↦ hx (mem_freeVars_app.mpr (Or.inr h))
      simp only [substTerm, ihr hr, ihs hs]

theorem substFormula_eq_of_not_free_of_closed (A : Formula) (x : Var) (t : Term)
    (hClosed : IsClosedTerm t) (hx : x ∉ freeVarsFormula A) : substFormula A x t = A := by
  induction A with
  | bot | varX => simp only [substFormula]
  | atom r =>
      simp only [substFormula]
      exact congrArg Formula.atom (substTerm_eq_of_not_free_of_closed r x t hClosed hx)
  | imp A B ihA ihB =>
      have hA : x ∉ freeVarsFormula A := by
        intro h
        exact hx (List.mem_eraseDups.mpr (List.mem_append_left _ h))
      have hB : x ∉ freeVarsFormula B := by
        intro h
        exact hx (List.mem_eraseDups.mpr (List.mem_append_right _ h))
      simp only [substFormula, ihA hA, ihB hB]
  | all y A ih =>
      by_cases hyx : y = x
      · simp [substFormula, hyx]
      · have hx' : x ∉ freeVarsFormula A := by
          intro h
          exact hx (List.mem_filter.mpr ⟨h, by simpa only [bne_iff_ne] using Ne.symm hyx⟩)
        simpa only [substFormula, beq_iff_eq, hyx, ↓reduceIte,
          not_mem_freeVarOccurrences_of_closed hClosed y] using congrArg (Formula.all y) (ih hx')

/-- Discharge object variables by universal introduction followed by instantiation
at canonical closed terms. -/
def closeVars : List Var → ProofTerm → ProofTerm
  | [], M => M
  | x :: xs, M => .appTerm (.lamTerm x (closeVars xs M)) (defaultTerm x.ty)

theorem freeAssumpVars_closeVars (xs : List Var) (M : ProofTerm) :
    freeAssumpVars (closeVars xs M) = freeAssumpVars M := by
  induction xs <;> simp_all [closeVars, freeAssumpVars]

theorem mem_objectSupport_closeVars {xs : List Var} {M : ProofTerm} {x : Var} :
    x ∈ objectSupport (closeVars xs M) ↔ x ∈ objectSupport M ∧ x ∉ xs := by
  induction xs with
  | nil => simp [closeVars]
  | cons y ys ih =>
      simp only [closeVars, objectSupport, defaultTerm_freeVars, List.append_nil,
        List.mem_filter, bne_iff_ne, ih, List.mem_cons, not_or]
      exact ⟨fun ⟨⟨hM, hys⟩, hxy⟩ ↦ ⟨hM, hxy, hys⟩,
        fun ⟨hM, hxy, hys⟩ ↦ ⟨⟨hM, hys⟩, hxy⟩⟩

theorem derivable_closeVars {sys : SysConfig} {M : ProofTerm} {B : Formula}
    (hM : Derivable sys M B) (hClosed : freeAssumpVars M = [])
    (xs : List Var) (hFresh : ∀ x ∈ xs, x ∉ freeVarsFormula B) :
    Derivable sys (closeVars xs M) B := by
  induction xs with
  | nil => exact hM
  | cons x xs ih =>
      have hInner := ih (fun y hy ↦ hFresh y (List.mem_cons_of_mem x hy))
      have hAll : Derivable sys (.lamTerm x (closeVars xs M)) (.all x B) := by
        apply Derivable.lamTerm x _ hInner
        intro u hu
        rw [freeAssumpVars_closeVars, hClosed] at hu
        cases hu
      have hApp := Derivable.appTerm (defaultTerm x.ty) (defaultTerm_typed x.ty) hAll
      rw [substFormula_eq_of_not_free_of_closed B x (defaultTerm x.ty)
        (defaultTerm_freeVars x.ty) (hFresh x (List.mem_cons_self ..))] at hApp
      exact hApp

/-- A closed-assumption proof can be normalized simultaneously for naming hygiene and
for support of its extracted program. Neither normalization uses realizability soundness. -/
theorem exists_supported_admissible_proof {sys : SysConfig} {M : ProofTerm} {B : Formula}
    (hM : Derivable sys M B) (hClosed : freeAssumpVars M = [])
    (ν : Ty) (dummy : Term) (hDummyTy : HasType dummy ν)
    (hDummyClosed : IsClosedTerm dummy) :
    ∃ N : ProofTerm, Derivable sys N B ∧ freeAssumpVars N = [] ∧
      AdmissibleForExtraction ν dummy N ∧
      ∀ x ∈ objectSupport N, x ∈ freeVarsFormula B := by
  let xs := (objectSupport M).filter (fun x ↦ decide (x ∉ freeVarsFormula B))
  let P := closeVars xs M
  let N := Hygiene.freshen (Hygiene.maxObjectId P + 1) P
  have hP : Derivable sys P B := by
    apply derivable_closeVars hM hClosed xs
    intro x hx
    exact of_decide_eq_true (List.mem_filter.mp hx).2
  refine ⟨N, Hygiene.derivable_relabel hP _, ?_,
    Hygiene.freshen_admissible ν dummy P hDummyTy hDummyClosed, ?_⟩
  · apply Hygiene.closed_relabel
    exact (freeAssumpVars_closeVars xs M).trans hClosed
  · intro x hx
    change x ∈ objectSupport (Hygiene.relabel _ P) at hx
    rw [objectSupport_relabel] at hx
    obtain ⟨hM, hxs⟩ := mem_objectSupport_closeVars.mp hx
    by_cases hB : x ∈ freeVarsFormula B
    · exact hB
    · exact False.elim (hxs (List.mem_filter.mpr
        ⟨hM, by simpa only [decide_eq_true_eq] using hB⟩))

end BBS2002.V2.Support


/- Local checked proof module: Soundness41Logic -/

namespace BBS2002.V2.Soundness41

/-- Alpha-renaming expressed with capture-avoiding substitution requires freshness
only for free variables; a globally fresh intermediate binder handles inner clashes. -/
theorem all_rename_of_not_free (A : Formula) (x y : Var)
    (hTy : x.ty = y.ty) (hy : y ∉ freeVarsFormula A) :
    FormulaBetaREq (.all x A) (.all y (substFormula A x (.var y))) := by
  obtain ⟨z, hzTy, hz⟩ := FormulaConversion.exists_fresh_var
    (allVarsFormula A ++ allVarsFormula (substFormula A x (.var y))) x.ty
  apply all_betaREq_of_fresh_subst A (substFormula A x (.var y)) x y z
    hzTy.symm (hTy.symm.trans hzTy.symm)
    (fun h ↦ hz (List.mem_append_left _ h))
    (fun h ↦ hz (List.mem_append_right _ h))
  have h := FormulaConversion.subst_formula_comprehension A x y (.var y) (.var z) (.inr hy)
  simpa only [substTerm, beq_self_eq_true, ↓reduceIte] using h.symm

/-- Universal realizability of a lambda is the expected quantified matrix.
The two general MR structural laws remain explicit until independently proved. -/
theorem mr_all_lambda (ν : Ty) (comp : CompTerm ν)
    (hc : ∀ A, MRCompatible ν comp A) (hs : ∀ A, MRSubstitution ν comp A)
    (x : Var) (A : Formula) (ρ : Ty) (hA : tau ν A = some ρ) (t : Term)
    (r : Realizer (tau ν (.all x A))) (hr : r.toOption = some (.lam x t))
    (hxC : x = comp.var ∨ x ∉ freeVarsFormula comp.body) :
    FormulaBetaREq (mrFormula ν comp (.all x A) r)
      (.all x (mrFormula ν comp A (Realizer.cast hA.symm t))) := by
  let a : Realizer (tau ν A) := Realizer.cast hA.symm t
  let y := freshVar comp r.toOption (.all x A) .bot x.ty
  have hyA : y ∉ allVarsFormula A := by
    intro h
    exact freshVar_not_mem_allVars_left comp r.toOption (.all x A) .bot x.ty
      (List.mem_cons_of_mem x h)
  have hyT : y ∉ allVarsTerm t := by
    have h := freshVar_not_mem_realizer comp (.lam x t) (.all x A) .bot x.ty
    change y ∉ allVarsTerm t
    intro hy
    apply h
    have hyt : y ∈ allVarsTerm (.lam x t) := List.mem_cons_of_mem x hy
    simpa only [y, hr] using hyt
  have hyMR : y ∉ freeVarsFormula (mrFormula ν comp A a) := by
    apply mrFormula_not_free ν comp A a y
      (fun h ↦ hyA (mem_freeVarsFormula_allVars h))
    · intro q hq hyq
      have ha : a.toOption = some t := Realizer.toOption_cast hA.symm t
      rw [ha] at hq
      have heq : q = t := (Option.some.inj (Option.mem_def.mp hq)).symm
      subst q
      exact hyT (mem_freeVarOccurrences_of_mem_allVars
        (by simpa only [freeVars, List.mem_eraseDups] using hyq))
    · exact .inr (freshVar_not_free_compBody comp r.toOption (.all x A) .bot x.ty)
  have hRename := all_rename_of_not_free (mrFormula ν comp A a) x y rfl hyMR
  rw [mrFormula.eq_def ν comp (.all x A) r]
  dsimp only
  split
  · rename_i hNone
    rw [hA] at hNone
    cases hNone
  · rename_i σ hσ
    have hσρ : σ = ρ := Option.some.inj (hσ.symm.trans hA)
    subst σ
    let f : Term := Realizer.cast (σ := some (.arr x.ty ρ)) (by simp only [tau, hσ]) r
    have hf : f = .lam x t := by
      apply Option.some.inj
      exact (Realizer.toOption_cast (σ := some (.arr x.ty ρ))
        (by simp only [tau, hσ]) r).trans hr
    refine FormulaBetaREq.trans (.all y ?_) hRename.symm
    apply FormulaBetaREq.trans _ (hs A a x (.var y) hxC).symm
    apply hc (renameFreeVarFormula A x y) (substFormula A x (.var y))
      (by rw [Conversion.subst_formula_fresh_var A x y hyA]; exact .refl _)
    change Option.Rel BetaREq
      (Realizer.cast ((tau_renameFreeVarFormula ν A x y).trans hσ).symm (.app f (.var y))).toOption
      (Realizer.cast (tau_substFormula ν A x (.var y)).symm (Realizer.subst a x (.var y))).toOption
    have hLeft : (Realizer.cast ((tau_renameFreeVarFormula ν A x y).trans hσ).symm
        (.app f (.var y))).toOption = some (.app f (.var y)) :=
      Realizer.toOption_cast (τ := some ρ) _ _
    rw [hLeft, Realizer.toOption_cast (tau_substFormula ν A x (.var y)).symm
      (Realizer.subst a x (.var y)), Realizer.subst_toOption]
    have ha : a.toOption = some t := Realizer.toOption_cast hA.symm t
    rw [ha]
    change Option.Rel BetaREq (some (.app f (.var y))) (some (substTerm t x (.var y)))
    rw [hf]
    exact .some (.of_conv (.beta x t (.var y)))

theorem mr_imp_lambda (ν : Ty) (comp : CompTerm ν)
    (hc : ∀ A, MRCompatible ν comp A) (hs : ∀ A, MRSubstitution ν comp A)
    (A B : Formula) (ρ σ : Ty) (hA : tau ν A = some ρ) (hB : tau ν B = some σ)
    (w : Var) (hwTy : w.ty = ρ) (t : Term)
    (r : Realizer (tau ν (.imp A B))) (hr : r.toOption = some (.lam w t))
    (hwA : w ∉ freeVarsFormula A) (hwB : w ∉ freeVarsFormula B)
    (hwC : w = comp.var ∨ w ∉ freeVarsFormula comp.body) :
    FormulaBetaREq (mrFormula ν comp (.imp A B) r)
      (.all w (.imp
        (mrFormula ν comp A (Realizer.cast hA.symm (.var w)))
        (mrFormula ν comp B (Realizer.cast hB.symm t)))) := by
  let a : Realizer (tau ν A) := Realizer.cast hA.symm (.var w)
  have ha : a.toOption = some (.var w) := Realizer.toOption_cast hA.symm (.var w)
  have hRFree : ∀ f ∈ r.toOption, w ∉ freeVars f := by
    intro f hf
    have hf' : f = .lam w t := Option.some.inj ((Option.mem_def.mp hf).symm.trans hr)
    subst f
    simp only [freeVars, List.mem_eraseDups, freeVarOccurrences, List.mem_filter, bne_iff_ne]
    exact fun ⟨_, hne⟩ ↦ hne rfl
  refine (mr_imp_fresh ν comp A B ⟨hc A, hs A⟩ ⟨hc B, hs B⟩ ρ hA r w hwTy
    hwA hwB hRFree hwC).trans (.all w (.imp (.refl _) ?_))
  apply hc B B (.refl B)
  have hApp := applyImp_toOption_some_arg ν A B r a (.var w) ha
  rw [hr] at hApp
  have hOut : (Realizer.cast hB.symm t).toOption = some t := Realizer.toOption_cast hB.symm t
  change Option.Rel BetaREq (Realizer.applyImp ν A B r a).toOption (Realizer.cast hB.symm t).toOption
  rw [hApp, hOut]
  apply Option.Rel.some
  have hBeta := BetaREq.of_conv (ConvStep.beta w t (.var w))
  rwa [substTerm_var_self] at hBeta

theorem mr_imp_epsilon (ν : Ty) (comp : CompTerm ν)
    (hc : ∀ A, MRCompatible ν comp A)
    (A B : Formula) (σ : Ty) (hA : tau ν A = none) (hB : tau ν B = some σ)
    (t : Term) (r : Realizer (tau ν (.imp A B))) (hr : r.toOption = some t) :
    FormulaBetaREq (mrFormula ν comp (.imp A B) r)
      (.imp (mrFormula ν comp A (Realizer.cast hA.symm ()))
        (mrFormula ν comp B (Realizer.cast hB.symm t))) := by
  rw [mrFormula_imp_none_some ν comp A B σ hA hB r]
  apply FormulaBetaREq.imp (.refl _)
  apply hc B B (.refl B)
  have hLeft : (Realizer.cast (show tau ν (.imp A B) = tau ν B by simp only [tau, hA]) r).toOption = some t :=
    (Realizer.toOption_cast _ r).trans hr
  have hRight : (Realizer.cast hB.symm t).toOption = some t := Realizer.toOption_cast hB.symm t
  rw [hLeft, hRight]
  exact .some (.refl t)


/-- Derivability under a predicate on permitted free assumption formulas. -/
def ContextDerivable (Γ : Formula → Prop) (A : Formula) : Prop :=
  ∃ N, Derivable SysConfig.Z N A ∧ ∀ v ∈ freeAssumpVars N, Γ v.formula

namespace ContextDerivable

theorem hyp {Γ : Formula → Prop} {A : Formula}
    (hA : SysConfig.Z.allowsFormula A) (hΓ : Γ A) : ContextDerivable Γ A := by
  refine ⟨.assump ⟨0, A⟩, .assump _ hA, ?_⟩
  intro v hv
  have hv' : v = ⟨0, A⟩ := by simpa only [freeAssumpVars, List.mem_singleton] using hv
  subst v
  exact hΓ

theorem mono {Γ Δ : Formula → Prop} {A : Formula}
    (h : ContextDerivable Γ A) (hΓΔ : ∀ D, Γ D → Δ D) : ContextDerivable Δ A := by
  obtain ⟨N, hN, hfree⟩ := h
  exact ⟨N, hN, fun v hv ↦ hΓΔ v.formula (hfree v hv)⟩

theorem closed {Γ : Formula → Prop} {A : Formula}
    (h : Provable SysConfig.Z A) : ContextDerivable Γ A := by
  obtain ⟨N, hN, hfree⟩ := h
  exact ⟨N, hN, fun v hv ↦ by rw [hfree] at hv; cases hv⟩

theorem mp {Γ : Formula → Prop} {A B : Formula}
    (hAB : ContextDerivable Γ (.imp A B)) (hA : ContextDerivable Γ A) :
    ContextDerivable Γ B := by
  obtain ⟨M, hM, hMf⟩ := hAB
  obtain ⟨N, hN, hNf⟩ := hA
  refine ⟨.appAssump M N, .appAssump hM hN, ?_⟩
  intro v hv
  rcases mem_freeAssumpVars_appAssump.mp hv with hv | hv
  · exact hMf v hv
  · exact hNf v hv

theorem conv {Γ : Formula → Prop} {A B : Formula}
    (hA : ContextDerivable Γ A) (hB : SysConfig.Z.allowsFormula B)
    (heq : FormulaBetaREq A B) : ContextDerivable Γ B := by
  obtain ⟨N, hN, hNf⟩ := hA
  exact ⟨N, .conv hN hB heq, hNf⟩

theorem imp_intro {Γ : Formula → Prop} {A B : Formula}
    (hA : SysConfig.Z.allowsFormula A)
    (h : ContextDerivable (fun D ↦ D = A ∨ Γ D) B) :
    ContextDerivable Γ (.imp A B) := by
  obtain ⟨N, hN, hNf⟩ := h
  let f : AssumpVar → Nat := fun _ ↦ 0
  let u : AssumpVar := ⟨0, A⟩
  refine ⟨.lamAssump u (Hygiene.relabel f N),
    .lamAssump u hA (Hygiene.derivable_relabel hN f), ?_⟩
  intro v hv
  obtain ⟨hv, hne⟩ := mem_freeAssumpVars_lamAssump.mp hv
  obtain ⟨w, hw, hvw⟩ := Hygiene.freeAssumpVars_relabel hv
  have heq : v.formula = w.formula := by
    simpa only [Hygiene.relabelVar] using congrArg AssumpVar.formula hvw
  rcases hNf w hw with hWA | hΓ
  · exfalso
    apply hne
    rw [hvw]
    change (⟨0, w.formula⟩ : AssumpVar) = ⟨0, A⟩
    rw [hWA]
  · exact heq ▸ hΓ

theorem all_intro {Γ : Formula → Prop} {A : Formula} (x : Var)
    (hx : ∀ D, Γ D → x ∉ freeVarsFormula D)
    (h : ContextDerivable Γ A) : ContextDerivable Γ (.all x A) := by
  obtain ⟨N, hN, hNf⟩ := h
  exact ⟨.lamTerm x N, .lamTerm x (fun v hv ↦ hx v.formula (hNf v hv)) hN, hNf⟩

theorem all_elim {Γ : Formula → Prop} {A : Formula} (x : Var) (t : Term)
    (ht : HasType t x.ty) (h : ContextDerivable Γ (.all x A)) :
    ContextDerivable Γ (substFormula A x t) := by
  obtain ⟨N, hN, hNf⟩ := h
  exact ⟨.appTerm N t, .appTerm t ht hN, hNf⟩

end ContextDerivable

/-- Formula conversion may introduce syntactically free variables which disappear
under beta conversion. The binder law only needs semantic independence of its source. -/
theorem mr_imp_fresh_invariant (ν : Ty) (comp : CompTerm ν) (A B : Formula)
    (ρ : Ty) (hA : tau ν A = some ρ) (r : Realizer (tau ν (.imp A B)))
    (w : Var) (hwTy : w.ty = ρ)
    (hwA : w ∉ freeVarsFormula A)
    (hwB : ∀ t, FormulaBetaREq (substFormula B w t) B)
    (hwR : ∀ f ∈ r.toOption, w ∉ freeVars f)
    (hwC : w = comp.var ∨ w ∉ freeVarsFormula comp.body) :
    let a : Realizer (tau ν A) := Realizer.cast (τ := some ρ) hA.symm (Term.var w)
    FormulaBetaREq (mrFormula ν comp (.imp A B) r)
      (.all w (.imp (mrFormula ν comp A a)
        (mrFormula ν comp B (Realizer.applyImp ν A B r a)))) := by
  let B₀ := substFormula B w (defaultTerm w.ty)
  have eB : FormulaBetaREq B₀ B := hwB (defaultTerm w.ty)
  have hwB₀ : w ∉ freeVarsFormula B₀ := by
    intro hw
    rcases Support.subst_formula_support B w (defaultTerm w.ty) w hw with ⟨_, hne⟩ | hw
    · exact hne rfl
    · rw [Support.defaultTerm_freeVars] at hw
      cases hw
  have hτ : tau ν (.imp A B₀) = tau ν (.imp A B) := by
    simp only [B₀, tau, tau_substFormula]
  let r₀ : Realizer (tau ν (.imp A B₀)) := Realizer.cast hτ.symm r
  have hr₀ : r₀.toOption = r.toOption := Realizer.toOption_cast hτ.symm r
  have hwR₀ : ∀ f ∈ r₀.toOption, w ∉ freeVars f := by
    simpa only [hr₀] using hwR
  refine FormulaBetaREq.trans (mrFormula_congr ν comp (.imp A B) (.imp A B₀) r r₀
    (.imp (.refl _) eB.symm) ?_) ?_
  · rw [hr₀]
    exact Realizer.toOption_rel_refl r
  refine (mr_imp_fresh ν comp A B₀ (mrFormula_transport_laws ν comp A)
    (mrFormula_transport_laws ν comp B₀) ρ hA r₀ w hwTy hwA hwB₀ hwR₀ hwC).trans ?_
  apply FormulaBetaREq.all w
  apply FormulaBetaREq.imp (.refl _)
  apply mrFormula_congr ν comp B₀ B _ _ eB
  rw [Realizer.applyImp_toOption, Realizer.applyImp_toOption, hr₀]
  cases r.toOption <;> cases (Realizer.cast (τ := some ρ) hA.symm (Term.var w)).toOption <;>
    first | exact Option.Rel.none | exact Option.Rel.some (.refl _)

theorem mr_all_lam (ν : Ty) (comp : CompTerm ν) (x : Var) (A : Formula)
    (r : Realizer (tau ν (.all x A))) (a : Realizer (tau ν A))
    (hr : r.toOption = a.toOption.map (Term.lam x))
    (hxC : x = comp.var ∨ x ∉ freeVarsFormula comp.body) :
    FormulaBetaREq (mrFormula ν comp (.all x A) r) (.all x (mrFormula ν comp A a)) := by
  cases hA : tau ν A with
  | none =>
      have ha : a.toOption = none := Realizer.toOption_eq_none a hA
      have hr' : r.toOption = none := by simpa only [ha, Option.map_none] using hr
      refine (mr_all_fresh ν comp x A (fun C _ ↦ mrFormula_transport_laws ν comp C)
        r x rfl (not_mem_freeVarsFormula_all x A) ?_ hxC).trans (.all x ?_)
      · intro f hf
        rw [hr'] at hf
        cases hf
      · apply mrFormula_congr ν comp (substFormula A x (.var x)) A _ _
          (by rw [substFormula_var_self]; exact .refl _)
        rw [Realizer.applyAll_toOption, hr', ha]
        exact .none
  | some ρ =>
      let t : Term := Realizer.cast hA a
      have ha : a.toOption = some t := (Realizer.toOption_cast hA a).symm
      have hr' : r.toOption = some (.lam x t) := by simpa only [ha, Option.map_some] using hr
      refine (mr_all_lambda ν comp (mrFormula_compatible ν comp) (mrFormula_substitution ν comp)
        x A ρ hA t r hr' hxC).trans (.all x ?_)
      apply mrFormula_congr ν comp A A _ _ (.refl _)
      rw [Realizer.toOption_cast, ha]
      exact .some (.refl _)

theorem mr_imp_lam (ν : Ty) (comp : CompTerm ν) (u : AssumpVar) (B : Formula)
    (r : Realizer (tau ν (.imp u.formula B))) (b : Realizer (tau ν B))
    (hr : r.toOption = match tau ν u.formula with
      | none => b.toOption
      | some ρ => b.toOption.map (Term.lam (⟨u.id, ρ⟩ : Var)))
    (hSource : ∀ ρ, (⟨u.id, ρ⟩ : Var) ∉ freeVarsFormula u.formula)
    (hInvariant : ∀ ρ t, FormulaBetaREq (substFormula B ⟨u.id, ρ⟩ t) B)
    (hComp : ∀ ρ, (⟨u.id, ρ⟩ : Var) = comp.var ∨
      (⟨u.id, ρ⟩ : Var) ∉ freeVarsFormula comp.body) :
    FormulaBetaREq (mrFormula ν comp (.imp u.formula B) r)
      (match tau ν u.formula with
      | none => .imp (mrFormula ν comp u.formula (assumpRealizer ν u)) (mrFormula ν comp B b)
      | some ρ => .all ⟨u.id, ρ⟩
          (.imp (mrFormula ν comp u.formula (assumpRealizer ν u)) (mrFormula ν comp B b))) := by
  cases hA : tau ν u.formula with
  | none =>
      simp only [hA] at hr ⊢
      rw [mrFormula_imp_none ν comp u.formula B hA r (assumpRealizer ν u)]
      apply FormulaBetaREq.imp (.refl _)
      apply mrFormula_congr ν comp B B _ _ (.refl _)
      have ha : (assumpRealizer ν u).toOption = none :=
        Realizer.toOption_eq_none _ hA
      rw [Realizer.applyImp_toOption, ha, hr]
      cases b.toOption <;> first | exact .none | exact .some (.refl _)
  | some ρ =>
      simp only [hA] at hr ⊢
      let w : Var := ⟨u.id, ρ⟩
      have hwR : ∀ f ∈ r.toOption, w ∉ freeVars f := by
        intro f hf
        rw [hr] at hf
        cases hb : b.toOption with
        | none => simp only [hb, Option.map_none, Option.not_mem_none] at hf
        | some t =>
            have hf' : f = .lam w t := by
              simpa only [hb, Option.map_some, Option.mem_def, Option.some.injEq] using hf.symm
            subst f
            simp only [freeVars, List.mem_eraseDups, freeVarOccurrences, List.mem_filter, bne_iff_ne]
            exact fun ⟨_, hne⟩ ↦ hne rfl
      have har : (Realizer.cast (τ := some ρ) hA.symm (Term.var w)).toOption = some (.var w) :=
        Realizer.toOption_cast (τ := some ρ) hA.symm (Term.var w)
      refine (mr_imp_fresh_invariant ν comp u.formula B ρ hA r w rfl
        (hSource ρ) (hInvariant ρ) hwR (hComp ρ)).trans (.all w (.imp ?_ ?_))
      · apply mrFormula_congr ν comp u.formula u.formula _ _ (.refl _)
        rw [har, assumpRealizer_toOption]
        simp only [assumpRealizerTerm, assumpRealizerVar, hA, Option.map_some]
        exact .some (.refl _)
      · apply mrFormula_congr ν comp B B _ _ (.refl _)
        rw [Realizer.applyImp_toOption, har, hr]
        cases hb : b.toOption with
        | none => exact .none
        | some t =>
            apply Option.Rel.some
            have hbeta := BetaREq.of_conv (ConvStep.beta w t (.var w))
            rwa [substTerm_var_self] at hbeta

end BBS2002.V2.Soundness41


/- Local checked proof module: ExtractionTyping41 -/

namespace BBS2002.V2.ExtractionTyping41

private theorem exists_typed_lam {τ : Option Ty} (x : Var) (r : Realizer τ)
    (hr : r.Typed) :
    ∃ s : Realizer (τ.map (.arr x.ty)),
      s.toOption = r.toOption.map (Term.lam x) ∧ s.Typed := by
  cases τ with
  | none => exact ⟨(), rfl, True.intro⟩
  | some σ => exact ⟨Term.lam x r, rfl, HasType.lam x hr⟩

theorem efqTerm_typed (ν : Ty) (dummy : Term) (hDummy : HasType dummy ν) (ρ : Ty) :
    HasType (efqTerm ν dummy ρ) ρ := by
  by_cases h : ρ = ν
  · subst ρ
    simpa [efqTerm] using hDummy
  · simpa [efqTerm, h] using Support.defaultTerm_typed ρ

private theorem exists_typed_efq (ν : Ty) (dummy : Term) (hDummy : HasType dummy ν)
    (τ : Option Ty) :
    ∃ r : Realizer τ, r.toOption = τ.map (efqTerm ν dummy) ∧ r.Typed := by
  cases τ with
  | none => exact ⟨(), rfl, True.intro⟩
  | some ρ => exact ⟨efqTerm ν dummy ρ, rfl, efqTerm_typed ν dummy hDummy ρ⟩

theorem extractRaw_typed (ν : Ty) (dummy : Term) (hDummy : HasType dummy ν)
    {sys : SysConfig} {M : ProofTerm} {B : Formula} (hDeriv : Derivable sys M B) :
    ∃ r : Realizer (tau ν B), r.toOption = extractRaw ν dummy M ∧ r.Typed := by
  induction hDeriv with
  | assump u _ =>
      exact ⟨assumpRealizer ν u, assumpRealizer_toOption ν u, assumpRealizer_typed ν u⟩
  | indNat n A hn _ =>
      cases hτ : tau ν A with
      | none =>
          have h : tau ν (indNatFormula n A) = none := by
            simp only [indNatFormula, tau, tau_substFormula, hτ]
          refine ⟨Realizer.cast h.symm (), ?_, (Realizer.typed_cast h.symm ()).mpr trivial⟩
          exact (Realizer.toOption_cast h.symm ()).trans
            (by simp only [Realizer.toOption, extractRaw, hτ, Option.map_none])
      | some ρ =>
          have h : tau ν (indNatFormula n A) = some (Const.recNat ρ).ty := by
            simp only [indNatFormula, tau, tau_substFormula, hτ, hn, Const.ty]
          refine ⟨Realizer.cast h.symm (.const (.recNat ρ)), ?_, ?_⟩
          · exact (Realizer.toOption_cast h.symm (.const (.recNat ρ))).trans
              (by simp only [Realizer.toOption, extractRaw, hτ, Option.map_some])
          · exact (Realizer.typed_cast h.symm _).mpr (HasType.const (.recNat ρ))
  | indBool p A hp _ =>
      cases hτ : tau ν A with
      | none =>
          have h : tau ν (indBoolFormula p A) = none := by
            simp only [indBoolFormula, tau, tau_substFormula, hτ]
          refine ⟨Realizer.cast h.symm (), ?_, (Realizer.typed_cast h.symm ()).mpr trivial⟩
          exact (Realizer.toOption_cast h.symm ()).trans
            (by simp only [Realizer.toOption, extractRaw, hτ, Option.map_none])
      | some ρ =>
          have h : tau ν (indBoolFormula p A) = some (Const.recBool ρ).ty := by
            simp only [indBoolFormula, tau, tau_substFormula, hτ, hp, Const.ty]
          refine ⟨Realizer.cast h.symm (.const (.recBool ρ)), ?_, ?_⟩
          · exact (Realizer.toOption_cast h.symm (.const (.recBool ρ))).trans
              (by simp only [Realizer.toOption, extractRaw, hτ, Option.map_some])
          · exact (Realizer.typed_cast h.symm _).mpr (HasType.const (.recBool ρ))
  | axTrue => exact ⟨(), rfl, True.intro⟩
  | axFalse A _ =>
      simpa only [extractRaw, tau, Formula.falseAtom] using
        exists_typed_efq ν dummy hDummy (tau ν A)
  | efq A _ _ =>
      simpa only [extractRaw, tau] using exists_typed_efq ν dummy hDummy (tau ν A)
  | @lamAssump u M B _ _ ih =>
      obtain ⟨r, hr, ht⟩ := ih
      cases hA : tau ν u.formula with
      | none =>
          let h : tau ν B = tau ν (.imp u.formula B) := by simp only [tau, hA]
          refine ⟨Realizer.cast h r, ?_, (Realizer.typed_cast h r).mpr ht⟩
          simpa only [Realizer.toOption_cast, extractRaw, hA] using hr
      | some ρ =>
          obtain ⟨s, hs, hst⟩ := exists_typed_lam (⟨u.id, ρ⟩ : Var) r ht
          have heq : (tau ν B).map (.arr ρ) = tau ν (.imp u.formula B) := by
            simp only [tau, hA]
            cases tau ν B <;> rfl
          refine ⟨Realizer.cast heq s, ?_, (Realizer.typed_cast heq s).mpr hst⟩
          simp only [Realizer.toOption_cast, hs, hr, extractRaw, hA]
  | @appAssump M N A B _ _ ihM ihN =>
      obtain ⟨r, hr, ht⟩ := ihM
      obtain ⟨s, hs, hst⟩ := ihN
      refine ⟨Realizer.applyImp ν A B r s, ?_, Realizer.applyImp_typed ν A B r s ht hst⟩
      simp only [Realizer.applyImp_toOption, extractRaw, hr, hs]
      rfl
  | @lamTerm x M A _ _ ih =>
      obtain ⟨r, hr, ht⟩ := ih
      obtain ⟨s, hs, hst⟩ := exists_typed_lam x r ht
      have heq : (tau ν A).map (.arr x.ty) = tau ν (.all x A) := by
        simp only [tau]
        cases tau ν A <;> rfl
      refine ⟨Realizer.cast heq s, ?_, (Realizer.typed_cast heq s).mpr hst⟩
      simp only [Realizer.toOption_cast, hs, hr, extractRaw]
  | @appTerm M x A t ht _ ih =>
      obtain ⟨r, hr, hrt⟩ := ih
      refine ⟨Realizer.applyAll ν x A r t, ?_, Realizer.applyAll_typed ν x A r t hrt ht⟩
      simp only [Realizer.applyAll_toOption, extractRaw, hr]
  | conv _ _ hAB ih =>
      obtain ⟨r, hr, ht⟩ := ih
      refine ⟨Realizer.cast (tau_formulaBetaREq ν hAB) r, ?_, ?_⟩
      · simpa only [Realizer.toOption_cast] using hr
      · exact (Realizer.typed_cast _ r).mpr ht

theorem extractProgram_eq_extractRaw (ν : Ty) (dummy : Term) (hDummy : HasType dummy ν)
    {sys : SysConfig} {M : ProofTerm} {B : Formula} (hDeriv : Derivable sys M B) :
    extractProgram ν dummy M B = extractRaw ν dummy M := by
  obtain ⟨r, hr, _⟩ := extractRaw_typed ν dummy hDummy hDeriv
  unfold extractProgram
  generalize hτ : tau ν B = τ at r hr ⊢
  cases τ with
  | none => exact hr
  | some ρ => rfl

theorem derivable_allowed {sys : SysConfig} {M : ProofTerm} {B : Formula}
    (hDeriv : Derivable sys M B) : sys.allowsFormula B := by
  induction hDeriv with
  | assump _ hA => exact hA
  | indNat n A hn hA =>
      have hz : HasType (.const .zero) n.ty := by simpa [hn, Const.ty] using HasType.const .zero
      have hs : HasType (Term.succTerm (.var n)) n.ty := by
        rw [hn]
        exact HasType.app (HasType.const .succ) (hn ▸ HasType.var n)
      exact (hA.substFormula n hz).imp ((hA.imp (hA.substFormula n hs)).all n |>.imp (hA.all n))
  | indBool p A hp hA =>
      have ht : HasType (.const .trueConst) p.ty := by
        simpa [hp, Const.ty] using HasType.const .trueConst
      have hf : HasType (.const .falseConst) p.ty := by
        simpa [hp, Const.ty] using HasType.const .falseConst
      exact (hA.substFormula p ht).imp ((hA.substFormula p hf).imp (hA.all p))
  | axTrue => exact .trueAtom sys
  | axFalse _ hA => exact (SysConfig.allowsFormula.falseAtom sys).imp hA
  | efq _ _ hA => exact (SysConfig.allowsFormula.bot sys).imp hA
  | lamAssump _ hA _ ih => exact hA.imp ih
  | appAssump _ _ ih _ =>
      obtain ⟨hAB, hL⟩ := ih
      cases hAB with
      | imp _ hB =>
          refine ⟨hB, ?_⟩
          rcases hL with hX | hL
          · exact .inl hX
          · exact .inr (Bool.and_eq_true_iff.mp hL).2
  | lamTerm x _ _ ih => exact ih.all x
  | @appTerm M x A t ht _ ih =>
      have hA : sys.allowsFormula A := by
        obtain ⟨hAll, hL⟩ := ih
        cases hAll with
        | all _ hA => exact ⟨hA, hL⟩
      exact hA.substFormula x ht
  | conv _ hB _ _ => exact hB

end BBS2002.V2.ExtractionTyping41


/- Local checked proof module: SemanticSupport41 -/

namespace BBS2002.V2.SemanticSupport41

open FormulaView

theorem subst_all_elim_invariant (A : Formula) (x w : Var) (s t : Term)
    (h : FormulaBetaREq (substFormula (.all x A) w s) (.all x A))
    (ht : w ∉ freeVarOccurrences t) :
    FormulaBetaREq (substFormula (substFormula A x t) w s) (substFormula A x t) := by
  have hView := (FormulaConversion.observe_subst (.all x A) w s).symm.trans
    (FormulaConversion.observe_betaREq h)
  change ViewRel (.all x.ty (mapTerms (fun q ↦ substTerm q w s)
    (mapTerms (Term.lam x) (observe A)))) (.all x.ty (mapTerms (Term.lam x) (observe A))) at hView
  have hBodies := hView.all_inv.2
  have hApp := hBodies.map (fun q ↦ Term.app q t) (fun q ↦ Term.app q t)
    (fun _ _ hq ↦ BetaREq.app hq (.refl t))
  simp only [mapTerms_comp] at hApp
  apply FormulaConversion.betaREq_of_observe
  refine (FormulaConversion.observe_subst_twice A x w t s).trans ?_
  refine ViewRel.trans ?_ (hApp.trans ?_)
  · apply mapTerms_pointwise
    intro q _
    have hBeta := Conversion.subst_term_congr w
      (BetaREq.of_conv (.beta x q t)).symm (BetaREq.refl s)
    refine hBeta.trans ?_
    rw [substTerm.eq_def (.app (.lam x q) t) w s]
    exact .app (.refl _) (.of_alpha (substTerm_alphaEq_of_not_free t w s ht))
  · refine ViewRel.trans ?_ (FormulaConversion.observe_subst A x t).symm
    apply mapTerms_pointwise
    intro q _
    exact .of_conv (.beta x q t)

theorem not_free_subst_self_var (A : Formula) (w z : Var) (hzw : z ≠ w) :
    w ∉ freeVarsFormula (substFormula A w (.var z)) := by
  intro hw
  rcases Support.subst_formula_support A w (.var z) w hw with h | h
  · exact h.2 rfl
  · simp only [freeVars, freeVarOccurrences, mem_eraseDups_iff, List.mem_singleton] at h
    exact hzw h.symm

theorem subst_invariant_of_fresh_instance (A : Formula) (w z : Var) (hzw : z ≠ w)
    (h : FormulaBetaREq (substFormula A w (.var z)) A) (t : Term) :
    FormulaBetaREq (substFormula A w t) A :=
  (FormulaConversion.subst_formula_congr w h.symm (.refl t)).trans
    ((formula_subst_betaREq_of_not_free _ w t (not_free_subst_self_var A w z hzw)).trans h)

theorem subst_all_invariant (A : Formula) (x w : Var)
    (h : ∀ t, FormulaBetaREq (substFormula A w t) A) (t : Term) :
    FormulaBetaREq (substFormula (.all x A) w t) (.all x A) := by
  by_cases hxw : x = w
  · subst x
    rw [substFormula.eq_def]
    simp only [beq_self_eq_true, ↓reduceIte]
    exact .refl _
  · obtain ⟨z, _, hz⟩ := FormulaConversion.exists_fresh_var [x, w] w.ty
    have hzx : z ≠ x := fun he ↦ hz (by simp [he])
    have hzw : z ≠ w := fun he ↦ hz (by simp [he])
    apply subst_invariant_of_fresh_instance (.all x A) w z hzw _ t
    rw [substFormula.eq_def]
    simp only [beq_iff_eq, hxw, ↓reduceIte, freeVarOccurrences, List.mem_singleton,
      Ne.symm hzx]
    exact .all x (h (.var z))

theorem not_free_subst (A : Formula) (x w : Var) (t : Term)
    (hwA : w ∉ freeVarsFormula A) (hwt : w ∉ freeVarOccurrences t) :
    w ∉ freeVarsFormula (substFormula A x t) := by
  intro hw
  rcases Support.subst_formula_support A x t w hw with h | h
  · exact hwA h.1
  · exact hwt (mem_eraseDups_iff.mp h)

theorem not_free_indNatFormula (n : Var) (A : Formula) (w : Var)
    (hwn : w ≠ n) (hwA : w ∉ freeVarsFormula A) : w ∉ freeVarsFormula (indNatFormula n A) := by
  have hZero := not_free_subst A n w (.const .zero) hwA (by simp [freeVarOccurrences])
  have hSucc := not_free_subst A n w (Term.succTerm (.var n)) hwA (by
    simpa [Term.succTerm, freeVarOccurrences] using hwn)
  intro hw
  simp only [indNatFormula, freeVarsFormula, mem_eraseDups_iff, List.mem_append,
    List.mem_filter] at hw
  rcases hw with hw | hw | hw
  · exact hZero hw
  · rcases hw.1 with hw | hw
    · exact hwA hw
    · exact hSucc hw
  · exact hwA hw.1

theorem not_free_indBoolFormula (p : Var) (A : Formula) (w : Var)
    (hwA : w ∉ freeVarsFormula A) : w ∉ freeVarsFormula (indBoolFormula p A) := by
  have hTrue := not_free_subst A p w (.const .trueConst) hwA (by simp [freeVarOccurrences])
  have hFalse := not_free_subst A p w (.const .falseConst) hwA (by simp [freeVarOccurrences])
  intro hw
  simp only [indBoolFormula, freeVarsFormula, mem_eraseDups_iff, List.mem_append,
    List.mem_filter] at hw
  rcases hw with hw | hw | hw
  · exact hTrue hw
  · exact hFalse hw
  · exact hwA hw.1

theorem derivable_subst_invariant {sys : SysConfig} {M : ProofTerm} {B : Formula}
    (h : Derivable sys M B) (w : Var) (t : Term) (hw : w ∉ allVarsProof M) :
    FormulaBetaREq (substFormula B w t) B := by
  induction h generalizing w t with
  | assump u hu =>
      apply formula_subst_betaREq_of_not_free
      exact fun h ↦ hw (mem_freeVarsFormula_allVars h)
  | indNat n A hn hA =>
      apply formula_subst_betaREq_of_not_free
      apply not_free_indNatFormula n A w
      · exact fun h ↦ hw (by simp [allVarsProof, h])
      · exact fun h ↦ hw (List.mem_cons_of_mem n (mem_freeVarsFormula_allVars h))
  | indBool p A hp hA =>
      apply formula_subst_betaREq_of_not_free
      apply not_free_indBoolFormula p A w
      exact fun h ↦ hw (List.mem_cons_of_mem p (mem_freeVarsFormula_allVars h))
  | axTrue =>
      exact formula_subst_betaREq_of_not_free _ w t (by
        simp [freeVarsFormula, freeVars, freeVarOccurrences])
  | axFalse A hA =>
      rw [substFormula_imp]
      exact .imp (formula_subst_betaREq_of_not_free _ w t (by
        simp [Formula.falseAtom, freeVarsFormula, freeVars, freeVarOccurrences]))
        (formula_subst_betaREq_of_not_free A w t
        (fun h ↦ hw (mem_freeVarsFormula_allVars h)))
  | efq A hEfq hA =>
      rw [substFormula_imp]
      exact .imp (formula_subst_betaREq_of_not_free _ w t (by simp [freeVarsFormula]))
        (formula_subst_betaREq_of_not_free A w t
        (fun h ↦ hw (mem_freeVarsFormula_allVars h)))
  | lamAssump u hU hM ih =>
      rw [substFormula_imp]
      exact .imp (formula_subst_betaREq_of_not_free u.formula w t
        (fun h ↦ hw (List.mem_append_left _ (mem_freeVarsFormula_allVars h))))
        (ih w t (fun h ↦ hw (List.mem_append_right _ h)))
  | appAssump hM hN ihM ihN =>
      have h := ihM w t (fun h ↦ hw (List.mem_append_left _ h))
      exact (FormulaConversion.imp_inversion (by simpa only [substFormula_imp] using h)).2
  | lamTerm x hFresh hM ih =>
      apply subst_all_invariant
      exact fun s ↦ ih w s (fun h ↦ hw (List.mem_cons_of_mem x h))
  | appTerm t₀ ht hM ih =>
      apply subst_all_elim_invariant _ _ w t t₀
        (ih w t (fun h ↦ hw (List.mem_append_left _ h)))
      exact fun h ↦ hw (List.mem_append_right _ (mem_freeVarOccurrences_of_mem_allVars h))
  | conv hM hB hAB ih =>
      exact (FormulaConversion.subst_formula_congr w hAB.symm (.refl t)).trans
        ((ih w t hw).trans hAB)

end BBS2002.V2.SemanticSupport41


/- Local checked proof module: Soundness41Context -/

namespace BBS2002.V2.Soundness41

/-- Separation needed only for the first, syntax-directed proof of soundness. -/
def FreshComp (ν : Ty) (comp : CompTerm ν) (M : ProofTerm) : Prop :=
  (∀ x ∈ allVarsProof M, x = comp.var ∨ x ∉ freeVarsFormula comp.body) ∧
  (∀ u ∈ allAssumpVars M, ∀ ρ, (⟨u.id, ρ⟩ : Var) = comp.var ∨
    (⟨u.id, ρ⟩ : Var) ∉ freeVarsFormula comp.body)

def extractionContext (ν : Ty) (comp : CompTerm ν) (M : ProofTerm) (D : Formula) : Prop :=
  ∃ u ∈ freeAssumpVars M, D = mrFormula ν comp u.formula (assumpRealizer ν u)

theorem freeAssumpVars_subset_all {M : ProofTerm} {u : AssumpVar}
    (hu : u ∈ freeAssumpVars M) : u ∈ allAssumpVars M := by
  induction M with
  | assump _ => exact hu
  | indNat | indBool | axTrue | axFalse | efq => cases hu
  | lamAssump v M ih => exact List.mem_cons_of_mem v (ih (List.mem_filter.mp hu).1)
  | appAssump M N ihM ihN =>
      rcases mem_freeAssumpVars_appAssump.mp hu with hu | hu
      · exact List.mem_append_left _ (ihM hu)
      · exact List.mem_append_right _ (ihN hu)
  | lamTerm _ _ ih | appTerm _ _ ih => exact ih hu

theorem allAssumpVars_formula_vars {M : ProofTerm} {u : AssumpVar}
    (hu : u ∈ allAssumpVars M) {x : Var} (hx : x ∈ allVarsFormula u.formula) :
    x ∈ allVarsProof M := by
  induction M with
  | assump v =>
      have huv : u = v := List.mem_singleton.mp hu
      simpa only [huv, allVarsProof] using hx
  | indNat | indBool | axTrue | axFalse | efq => cases hu
  | lamAssump v M ih =>
      rcases List.mem_cons.mp hu with rfl | hu
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (ih hu)
  | appAssump M N ihM ihN =>
      rcases List.mem_append.mp hu with hu | hu
      · exact List.mem_append_left _ (ihM hu)
      · exact List.mem_append_right _ (ihN hu)
  | lamTerm y M ih => exact List.mem_cons_of_mem y (ih hu)
  | appTerm M t ih => exact List.mem_append_left _ (ih hu)

theorem admissible_mono (ν : Ty) (dummy : Term) {M N : ProofTerm}
    (h : AdmissibleForExtraction ν dummy M)
    (hA : ∀ u ∈ allAssumpVars N, u ∈ allAssumpVars M)
    (hO : ∀ x ∈ allVarsProof N, x ∈ allVarsProof M) :
    AdmissibleForExtraction ν dummy N :=
  ⟨h.1, h.2.1, fun u hu x hx ↦ h.2.2.1 u (hA u hu) x (hO x hx),
    fun u hu v hv ↦ h.2.2.2 u (hA u hu) v (hA v hv)⟩

theorem freshComp_mono (ν : Ty) (comp : CompTerm ν) {M N : ProofTerm}
    (h : FreshComp ν comp M)
    (hA : ∀ u ∈ allAssumpVars N, u ∈ allAssumpVars M)
    (hO : ∀ x ∈ allVarsProof N, x ∈ allVarsProof M) : FreshComp ν comp N :=
  ⟨fun x hx ↦ h.1 x (hO x hx), fun u hu ↦ h.2 u (hA u hu)⟩

theorem extractionContext_mono (ν : Ty) (comp : CompTerm ν) {M N : ProofTerm}
    (h : ∀ u ∈ freeAssumpVars M, u ∈ freeAssumpVars N) :
    ∀ D, extractionContext ν comp M D → extractionContext ν comp N D := by
  intro D ⟨u, hu, heq⟩
  exact ⟨u, h u hu, heq⟩

theorem assumpRealizer_not_free (ν : Ty) (u : AssumpVar) (x : Var)
    (hx : x.id ≠ u.id) : ∀ t ∈ (assumpRealizer ν u).toOption, x ∉ freeVars t := by
  rw [assumpRealizer_toOption]
  unfold assumpRealizerTerm assumpRealizerVar
  cases tau ν u.formula with
  | none => simp only [Option.map_none, Option.not_mem_none, false_implies, implies_true]
  | some ρ =>
      intro t ht hxt
      have ht' : t = .var ⟨u.id, ρ⟩ := by
        simpa only [Option.map_some, Option.mem_def, Option.some.injEq] using ht.symm
      subst t
      have heq : x = ⟨u.id, ρ⟩ := by simpa only [freeVars, freeVarOccurrences,
        List.mem_eraseDups, List.mem_singleton] using hxt
      exact hx (congrArg Var.id heq)

theorem extractionContext_object_fresh (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    {M : ProofTerm} (x : Var)
    (hAdm : AdmissibleForExtraction ν dummy (.lamTerm x M))
    (hFresh : FreshComp ν comp (.lamTerm x M))
    (hSource : ∀ u ∈ freeAssumpVars M, x ∉ freeVarsFormula u.formula) :
    ∀ D, extractionContext ν comp M D → x ∉ freeVarsFormula D := by
  intro D hD
  obtain ⟨u, hu, heq⟩ := hD
  rw [heq]
  apply mrFormula_not_free ν comp u.formula (assumpRealizer ν u) x (hSource u hu)
  · apply assumpRealizer_not_free ν u x
    exact Ne.symm (hAdm.2.2.1 u (freeAssumpVars_subset_all hu) x (List.mem_cons_self ..))
  · exact hFresh.1 x (List.mem_cons_self ..)

theorem extractionContext_assump_fresh (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    {M : ProofTerm} (u : AssumpVar) (ρ : Ty)
    (hAdm : AdmissibleForExtraction ν dummy (.lamAssump u M))
    (hFresh : FreshComp ν comp (.lamAssump u M)) :
    ∀ D, extractionContext ν comp (.lamAssump u M) D →
      (⟨u.id, ρ⟩ : Var) ∉ freeVarsFormula D := by
  intro D hD
  obtain ⟨v, hv, heq⟩ := hD
  rw [heq]
  obtain ⟨hvM, hvu⟩ := mem_freeAssumpVars_lamAssump.mp hv
  have hvAll : v ∈ allAssumpVars (.lamAssump u M) :=
    List.mem_cons_of_mem u (freeAssumpVars_subset_all hvM)
  apply mrFormula_not_free ν comp v.formula (assumpRealizer ν v) ⟨u.id, ρ⟩
  · intro hx
    have hxAll := allAssumpVars_formula_vars hvAll (mem_freeVarsFormula_allVars hx)
    exact hAdm.2.2.1 u (List.mem_cons_self ..) ⟨u.id, ρ⟩ hxAll rfl
  · apply assumpRealizer_not_free ν v ⟨u.id, ρ⟩
    intro hID
    have hFormula := hAdm.2.2.2 u (List.mem_cons_self ..) v hvAll hID
    apply hvu
    cases u
    cases v
    simp_all
  · exact hFresh.2 u (List.mem_cons_self ..) ρ

end BBS2002.V2.Soundness41


/- Local checked proof module: EasyAxioms41 -/

namespace BBS2002.V2.EasyAxioms41

theorem axTrue_realizes (ν : Ty) (comp : CompTerm ν)
    (r : Realizer (tau ν (.atom (.const .trueConst)))) :
    Provable SysConfig.Z (mrFormula ν comp (.atom (.const .trueConst)) r) := by
  rw [mrFormula.eq_def]
  exact ⟨.axTrue, .axTrue, rfl⟩

theorem axFalse_realizes (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (hA : FormulaWellTyped A) (r : Realizer (tau ν (.imp Formula.falseAtom A)))
    (hr : r.Typed) : Provable SysConfig.Z (mrFormula ν comp (.imp Formula.falseAtom A) r) := by
  rw [mrFormula_imp_none ν comp Formula.falseAtom A rfl r ()]
  rw [mrFormula.eq_def ν comp Formula.falseAtom ()]
  refine ⟨.axFalse _, .axFalse _ ?_, rfl⟩
  exact ⟨mrFormula_wellTyped ν comp A _ hA
    (Realizer.applyImp_typed ν Formula.falseAtom A r () hr trivial),
    .inr (mrFormula_isL ν comp A _)⟩

theorem efq_realizes (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (hA : FormulaWellTyped A) (r : Realizer (tau ν (.imp .bot A))) (hr : r.Typed) :
    Provable SysConfig.Z (mrFormula ν comp (.imp .bot A) r) := by
  rw [mrFormula_imp_none ν comp .bot A rfl r (), mrFormula.eq_def ν comp .bot ()]
  refine ⟨.efq _, .efq _ rfl ?_, rfl⟩
  exact ⟨mrFormula_wellTyped ν comp A _ hA
    (Realizer.applyImp_typed ν .bot A r () hr trivial),
    .inr (mrFormula_isL ν comp A _)⟩

end BBS2002.V2.EasyAxioms41


/- Local checked proof module: Logic51 -/

namespace BBS2002.V2.ComputationalLogic

theorem allows_append {sys : SysConfig} {Γ Δ : List Formula}
    (hΓ : ∀ A ∈ Γ, sys.allowsFormula A) (hΔ : ∀ A ∈ Δ, sys.allowsFormula A) :
    ∀ A ∈ Γ ++ Δ, sys.allowsFormula A := by
  intro A hA
  rcases List.mem_append.mp hA with hA | hA
  · exact hΓ A hA
  · exact hΔ A hA

theorem ctx_cut {sys : SysConfig} {Γ Δ : List Formula} {B : Formula}
    (hΓ : ∀ A ∈ Γ, sys.allowsFormula A) (hΔ : ∀ A ∈ Δ, sys.allowsFormula A)
    (hB : sys.allowsFormula B)
    (hArgs : ∀ A ∈ Δ, Provable sys (Formula.impMany Γ A))
    (hFn : Provable sys (Formula.impMany Γ (Formula.impMany Δ B))) :
    Provable sys (Formula.impMany Γ B) := by
  induction Δ with
  | nil => exact hFn
  | cons A Δ ih =>
      have hΔ' : ∀ C ∈ Δ, sys.allowsFormula C := fun C hC ↦ hΔ C (List.mem_cons_of_mem A hC)
      apply ih hΔ' (fun C hC ↦ hArgs C (List.mem_cons_of_mem A hC))
      exact Provable.ctx_mp hΓ (hΔ A (List.mem_cons_self ..)) (.impMany hΔ' hB)
        hFn (hArgs A (List.mem_cons_self ..))

/-- Reordering, weakening, and contraction of a curried formula context. -/
theorem ctx_mono {sys : SysConfig} {Γ Δ : List Formula} {B : Formula}
    (hΓ : ∀ A ∈ Γ, sys.allowsFormula A) (hΔ : ∀ A ∈ Δ, sys.allowsFormula A)
    (hB : sys.allowsFormula B) (hIncl : ∀ A ∈ Γ, A ∈ Δ)
    (h : Provable sys (Formula.impMany Γ B)) :
    Provable sys (Formula.impMany Δ B) :=
  ctx_cut hΔ hΓ hB (fun A hA ↦ Provable.ctx_hyp hΔ (hIncl A hA))
    (Provable.ctx_const hΔ h)

theorem allows_allMany {sys : SysConfig} (xs : List Var) {A : Formula}
    (hA : sys.allowsFormula A) : sys.allowsFormula (Formula.allMany xs A) := by
  induction xs with
  | nil => exact hA
  | cons x xs ih => exact ih.all x

theorem ctx_allMany_elim_self {sys : SysConfig} (Γ : List Formula) (xs : List Var)
    (A : Formula) (hΓ : ∀ B ∈ Γ, sys.allowsFormula B) (hA : sys.allowsFormula A)
    (h : Provable sys (Formula.impMany Γ (Formula.allMany xs A))) :
    Provable sys (Formula.impMany Γ A) := by
  induction xs with
  | nil => exact h
  | cons x xs ih =>
      apply ih
      exact Provable.ctx_mp hΓ ((allows_allMany xs hA).all x) (allows_allMany xs hA)
        (Provable.ctx_const hΓ (Provable.imp_all_elim_self x (allows_allMany xs hA))) h

theorem all_imp_out {sys : SysConfig} (x : Var) (D A : Formula)
    (hD : sys.allowsFormula D) (hA : sys.allowsFormula A)
    (hx : x ∉ freeVarsFormula D) :
    Provable sys (.imp (.all x (.imp D A)) (.imp D (.all x A))) := by
  let u : AssumpVar := ⟨0, .all x (.imp D A)⟩
  let v : AssumpVar := ⟨1, D⟩
  let P := ProofTerm.appAssump (.appTerm (.assump u) (.var x)) (.assump v)
  have hAll := Derivable.assump u ((hD.imp hA).all x)
  have hApp : Derivable sys (.appTerm (.assump u) (.var x)) (.imp D A) := by
    have h := Derivable.appTerm (.var x) (.var x) hAll
    rw [substFormula_var_self] at h
    exact h
  have hP : Derivable sys P A := .appAssump hApp (.assump v hD)
  have hPx : Derivable sys (.lamTerm x P) (.all x A) := by
    apply Derivable.lamTerm x _ hP
    intro w hw
    have hw' : w = u ∨ w = v := by
      simpa [P, freeAssumpVars, List.mem_eraseDups] using hw
    rcases hw' with rfl | rfl
    · exact not_mem_freeVarsFormula_all x (.imp D A)
    · exact hx
  refine ⟨.lamAssump u (.lamAssump v (.lamTerm x P)),
    .lamAssump u ((hD.imp hA).all x) (.lamAssump v hD hPx), ?_⟩
  simp [P, freeAssumpVars, u, v]

theorem all_impMany_out {sys : SysConfig} (x : Var) (Γ : List Formula) (A : Formula)
    (hΓ : ∀ D ∈ Γ, sys.allowsFormula D) (hA : sys.allowsFormula A)
    (hx : ∀ D ∈ Γ, x ∉ freeVarsFormula D) :
    Provable sys (.imp (.all x (Formula.impMany Γ A))
      (Formula.impMany Γ (.all x A))) := by
  induction Γ with
  | nil => exact Provable.id (hA.all x)
  | cons D Γ ih =>
      have hD := hΓ D (List.mem_cons_self ..)
      have hΓ' : ∀ E ∈ Γ, sys.allowsFormula E := fun E hE ↦ hΓ E (List.mem_cons_of_mem D hE)
      have hRest := ih hΓ' (fun E hE ↦ hx E (List.mem_cons_of_mem D hE))
      have hOut := all_imp_out x D (Formula.impMany Γ A) hD (.impMany hΓ' hA)
        (hx D (List.mem_cons_self ..))
      exact Provable.imp_trans ((hD.imp (.impMany hΓ' hA)).all x)
        (hD.imp ((SysConfig.allowsFormula.impMany hΓ' hA).all x))
        (hD.imp (.impMany hΓ' (hA.all x))) hOut
        (Provable.imp_congr hD hD ((SysConfig.allowsFormula.impMany hΓ' hA).all x)
          (.impMany hΓ' (hA.all x)) (Provable.id hD) hRest)

theorem ctx_allMany_intro {sys : SysConfig} (Γ : List Formula) (xs : List Var)
    (A : Formula) (hΓ : ∀ D ∈ Γ, sys.allowsFormula D) (hA : sys.allowsFormula A)
    (hx : ∀ x ∈ xs, ∀ D ∈ Γ, x ∉ freeVarsFormula D)
    (h : Provable sys (Formula.impMany Γ A)) :
    Provable sys (Formula.impMany Γ (Formula.allMany xs A)) := by
  induction xs with
  | nil => exact h
  | cons x xs ih =>
      have hTail := ih (fun y hy ↦ hx y (List.mem_cons_of_mem x hy))
      exact Provable.mp (all_impMany_out x Γ _ hΓ (allows_allMany xs hA)
        (hx x (List.mem_cons_self ..))) (Provable.all_intro x hTail)

theorem impMany_map_congr (Γ : List Formula) (f g : Formula → Formula) {A B : Formula}
    (hΓ : ∀ C ∈ Γ, FormulaBetaREq (f C) (g C)) (hAB : FormulaBetaREq A B) :
    FormulaBetaREq (Formula.impMany (Γ.map f) A) (Formula.impMany (Γ.map g) B) := by
  induction Γ with
  | nil => exact hAB
  | cons C Γ ih =>
      exact .imp (hΓ C (List.mem_cons_self ..))
        (ih (fun D hD ↦ hΓ D (List.mem_cons_of_mem C hD)))

theorem ctx_conv {sys : SysConfig} {Γ : List Formula} {A B : Formula}
    (hΓ : ∀ C ∈ Γ, sys.allowsFormula C) (hB : sys.allowsFormula B)
    (hAB : FormulaBetaREq A B) (hA : Provable sys (Formula.impMany Γ A)) :
    Provable sys (Formula.impMany Γ B) := by
  have hEq : FormulaBetaREq (Formula.impMany Γ A) (Formula.impMany Γ B) := by
    clear hA hΓ
    induction Γ with
    | nil => exact hAB
    | cons C Γ ih => exact .imp (.refl C) ih
  exact Provable.conv hA (.impMany hΓ hB) hEq

theorem provable_substFormula {sys : SysConfig} {A : Formula} (x : Var) (t : Term)
    (ht : HasType t x.ty) (hA : Provable sys A) :
    Provable sys (substFormula A x t) := by
  obtain ⟨M, hM, hMC⟩ := Provable.all_intro x hA
  exact ⟨.appTerm M t, .appTerm t ht hM, hMC⟩

theorem substFormula_impMany (Γ : List Formula) (A : Formula) (x : Var) (t : Term) :
    substFormula (Formula.impMany Γ A) x t =
      Formula.impMany (Γ.map fun C ↦ substFormula C x t) (substFormula A x t) := by
  induction Γ with
  | nil => rfl
  | cons C Γ ih => simp only [Formula.impMany, substFormula, List.map_cons, ih]

theorem mem_formula_occurrences_iff (A : Formula) (x : Var) :
    x ∈ freeVarOccurrencesFormula A ↔ x ∈ freeVarsFormula A := by
  induction A with
  | bot | varX => rfl
  | atom t => simp only [freeVarOccurrencesFormula, freeVarsFormula, freeVars, List.mem_eraseDups]
  | imp A B ihA ihB =>
      simp only [freeVarOccurrencesFormula, freeVarsFormula, List.mem_eraseDups,
        List.mem_append, ihA, ihB]
  | all y A ih => simp only [freeVarOccurrencesFormula, freeVarsFormula, List.mem_filter, ih]

theorem subst_impMany_context_congr (Γ : List Formula) (A B : Formula) (x : Var) (t : Term)
    (hΓ : ∀ C ∈ Γ, x ∉ freeVarsFormula C)
    (hAB : FormulaBetaREq (substFormula A x t) B) :
    FormulaBetaREq (substFormula (Formula.impMany Γ A) x t) (Formula.impMany Γ B) := by
  rw [substFormula_impMany]
  have h := impMany_map_congr Γ (fun C ↦ substFormula C x t) id
    (fun C hC ↦ substFormula_betaREq_of_not_free C x t
      (fun hx ↦ hΓ C hC ((mem_formula_occurrences_iff C x).mp hx))) hAB
  simpa only [List.map_id] using h

/-- A source goal, its realizability premise, and the operation it performs on the
current candidate. This record is used only for a generic propositional induction. -/
structure GoalElimStep (α : Type) where
  goal : Formula
  premise : Formula
  apply : α → α

def goalResult {α : Type} (steps : List (GoalElimStep α)) (a : α) : α :=
  steps.foldr (fun step result ↦ step.apply result) a

/-- Compose goal eliminators in the order of the paper's nested term
`s₁ w₁ (... (sₘ wₘ a) ...)`. This is pure intuitionistic propositional logic. -/
theorem compose_goal_eliminators {sys : SysConfig} {α : Type}
    (C : α → Formula) (steps : List (GoalElimStep α)) (a : α) (Γ : List Formula)
    (hΓ : ∀ A ∈ Γ, sys.allowsFormula A)
    (hC : ∀ a, sys.allowsFormula (C a))
    (hG : ∀ step ∈ steps, sys.allowsFormula step.goal)
    (hR : ∀ step ∈ steps, sys.allowsFormula step.premise)
    (hStep : ∀ step ∈ steps, ∀ b : α,
      Provable sys (Formula.impMany Γ
        (.imp step.premise (.imp (.imp step.goal (C b)) (C (step.apply b))))))
    (hBase : Provable sys (Formula.impMany Γ
      (Formula.impMany (steps.map GoalElimStep.goal) (C a)))) :
    Provable sys (Formula.impMany Γ
      (Formula.impMany (steps.map GoalElimStep.premise) (C (goalResult steps a)))) := by
  induction steps generalizing Γ with
  | nil => exact hBase
  | cons step steps ih =>
      have hg : sys.allowsFormula step.goal := hG step (List.mem_cons_self ..)
      have hr : sys.allowsFormula step.premise := hR step (List.mem_cons_self ..)
      have hGs : ∀ s ∈ steps, sys.allowsFormula s.goal :=
        fun s hs ↦ hG s (List.mem_cons_of_mem step hs)
      have hRs : ∀ s ∈ steps, sys.allowsFormula s.premise :=
        fun s hs ↦ hR s (List.mem_cons_of_mem step hs)
      let Rs := steps.map GoalElimStep.premise
      have hRsAllowed : ∀ R ∈ Rs, sys.allowsFormula R := by
        intro R hR
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hR
        exact hRs s hs
      let Γ' := Γ ++ [step.goal]
      have hΓ' : ∀ A ∈ Γ', sys.allowsFormula A :=
        allows_append hΓ (by simpa only [List.mem_singleton] using fun _ h ↦ h ▸ hg)
      have hTail : Provable sys (Formula.impMany Γ'
          (Formula.impMany Rs (C (goalResult steps a)))) := by
        apply ih Γ' hΓ' hGs hRs
        · intro s hs b
          apply ctx_mono hΓ hΓ'
            ((hRs s hs).imp ((hGs s hs).imp (hC b) |>.imp (hC (s.apply b))))
            (fun A hA ↦ List.mem_append_left _ hA)
          exact hStep s (List.mem_cons_of_mem step hs) b
        · simpa only [Γ', impMany_append, List.map_cons, Formula.impMany] using hBase
      let Δ := Γ ++ (step.premise :: Rs)
      have hΔ : ∀ A ∈ Δ, sys.allowsFormula A := allows_append hΓ (by
        intro A hA
        rcases List.mem_cons.mp hA with rfl | hA
        · exact hr
        · exact hRsAllowed A hA)
      have hImp : Provable sys (Formula.impMany Δ
          (.imp step.goal (C (goalResult steps a)))) := by
        have hTail' : Provable sys (Formula.impMany (Γ' ++ Rs) (C (goalResult steps a))) := by
          simpa only [impMany_append] using hTail
        have hReorder : Provable sys
            (Formula.impMany (Δ ++ [step.goal]) (C (goalResult steps a))) := by
          apply ctx_mono (allows_append hΓ' hRsAllowed)
            (allows_append hΔ (by simpa only [List.mem_singleton] using fun _ h ↦ h ▸ hg))
            (hC _) _ hTail'
          intro A hA
          simp only [Γ', Δ, List.mem_append, List.mem_cons] at hA ⊢
          rcases hA with (hA | hA) | hA
          · exact Or.inl (Or.inl hA)
          · exact Or.inr hA
          · exact Or.inl (Or.inr (Or.inr hA))
        simpa only [impMany_append, Formula.impMany] using hReorder
      have hStepΔ : Provable sys (Formula.impMany Δ
          (.imp step.premise
            (.imp (.imp step.goal (C (goalResult steps a))) (C (goalResult (step :: steps) a))))) := by
        apply ctx_mono hΓ hΔ
          (hr.imp ((hg.imp (hC _)).imp (hC _)))
          (fun A hA ↦ List.mem_append_left _ hA)
        exact hStep step (List.mem_cons_self ..) (goalResult steps a)
      have hResult : Provable sys (Formula.impMany Δ (C (goalResult (step :: steps) a))) :=
        Provable.ctx_mp hΔ (hg.imp (hC _)) (hC _)
          (Provable.ctx_mp hΔ hr ((hg.imp (hC _)).imp (hC _)) hStepΔ
            (Provable.ctx_hyp hΔ (List.mem_append_right _ (List.mem_cons_self ..)))) hImp
      simpa only [Δ, impMany_append, List.map_cons] using hResult

/-- The alternating quantifiers and implications in a realizability goal matrix. -/
def quantifiedMatrix : List (Option Var × Formula) → Formula → Formula
  | [], C => C
  | (none, R) :: rest, C => .imp R (quantifiedMatrix rest C)
  | (some w, R) :: rest, C => .all w (.imp R (quantifiedMatrix rest C))

theorem quantifiedMatrix_allowed {sys : SysConfig} (pairs : List (Option Var × Formula))
    (C : Formula) (hC : sys.allowsFormula C)
    (hR : ∀ p ∈ pairs, sys.allowsFormula p.2) : sys.allowsFormula (quantifiedMatrix pairs C) := by
  induction pairs with
  | nil => exact hC
  | cons p pairs ih =>
      have ht := ih (fun q hq ↦ hR q (List.mem_cons_of_mem p hq))
      have hp := hR p (List.mem_cons_self ..)
      rcases p with ⟨w, R⟩
      cases w with
      | none => exact hp.imp ht
      | some w => exact (hp.imp ht).all w

/-- Insert each realizer quantifier immediately before its corresponding premise.
A later binder is fresh for the assumptions that precede it. -/
theorem quantify_matrix {sys : SysConfig} {n : Nat}
    (Γ : List Formula) (ws : Fin n → Option Var) (Rs : Fin n → Formula) (C : Formula)
    (hΓ : ∀ D ∈ Γ, sys.allowsFormula D) (hRs : ∀ i, sys.allowsFormula (Rs i))
    (hC : sys.allowsFormula C)
    (hFresh : ∀ i, ∀ w ∈ ws i, ∀ D ∈ Γ, w ∉ freeVarsFormula D)
    (hEarlier : ∀ i j, j.val < i.val → ∀ w ∈ ws i, w ∉ freeVarsFormula (Rs j))
    (h : Provable sys (Formula.impMany Γ (Formula.impMany (List.ofFn Rs) C))) :
    Provable sys (Formula.impMany Γ
      (quantifiedMatrix (List.ofFn fun i ↦ (ws i, Rs i)) C)) := by
  induction n generalizing Γ with
  | zero => exact h
  | succ n ih =>
      let Γ' := Γ ++ [Rs 0]
      have hΓ' : ∀ D ∈ Γ', sys.allowsFormula D :=
        allows_append hΓ (by simpa only [List.mem_singleton] using fun _ h ↦ h ▸ hRs 0)
      have hTail : Provable sys (Formula.impMany Γ'
          (quantifiedMatrix (List.ofFn fun i : Fin n ↦ (ws i.succ, Rs i.succ)) C)) := by
        apply ih Γ' (fun i ↦ ws i.succ) (fun i ↦ Rs i.succ) hΓ' (fun i ↦ hRs i.succ)
        · intro i w hw D hD
          rcases List.mem_append.mp hD with hD | hD
          · exact hFresh i.succ w hw D hD
          · have hD' : D = Rs 0 := List.mem_singleton.mp hD
            subst D
            exact hEarlier i.succ 0 (Nat.zero_lt_succ _) w hw
        · intro i j hji w hw
          exact hEarlier i.succ j.succ (Nat.succ_lt_succ hji) w hw
        · simpa only [Γ', impMany_append, Formula.impMany, List.ofFn_succ] using h
      have hTailAllowed : sys.allowsFormula
          (quantifiedMatrix (List.ofFn fun i : Fin n ↦ (ws i.succ, Rs i.succ)) C) := by
        apply quantifiedMatrix_allowed _ C hC
        intro p hp
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
        exact hRs i.succ
      have hTail' : Provable sys (Formula.impMany Γ
          (.imp (Rs 0) (quantifiedMatrix
            (List.ofFn fun i : Fin n ↦ (ws i.succ, Rs i.succ)) C))) := by
        simpa only [Γ', impMany_append, Formula.impMany] using hTail
      rw [List.ofFn_succ]
      cases hw0 : ws 0 with
      | none => exact hTail'
      | some w =>
          exact ctx_allMany_intro Γ [w] _ hΓ ((hRs 0).imp hTailAllowed)
            (by
              intro x hx D hD
              have hx' : x = w := List.mem_singleton.mp hx
              subst x
              exact hFresh 0 w (Option.mem_def.mpr hw0) D hD) hTail'

end BBS2002.V2.ComputationalLogic


/- Local checked proof module: InductionRealizers41 -/

namespace BBS2002.V2

/-- Universal elimination commutes with the capture-avoiding realizability translation. -/
theorem mr_all_elim (ν : Ty) (comp : CompTerm ν) (x : Var) (A : Formula)
    (r : Realizer (tau ν (.all x A))) (t : Term)
    (ht : HasType t x.ty) (hA : FormulaWellTyped A) (hr : r.Typed) :
    Provable SysConfig.Z (.imp (mrFormula ν comp (.all x A) r)
      (mrFormula ν comp (substFormula A x t) (Realizer.applyAll ν x A r t))) := by
  let u := freshVar comp r.toOption (.all x A) .bot x.ty
  let P := mrFormula ν comp (substFormula A x (.var u))
    (Realizer.applyAll ν x A r (.var u))
  have hP := MrLogic.mr_allowed ν comp (substFormula A x (.var u))
    (Realizer.applyAll ν x A r (.var u)) (hA.substFormula x (.var u))
    (Realizer.applyAll_typed ν x A r (.var u) hr (.var u))
  have hQ := MrLogic.mr_allowed ν comp (substFormula A x t)
    (Realizer.applyAll ν x A r t) (hA.substFormula x ht)
    (Realizer.applyAll_typed ν x A r t hr ht)
  have huA : u = x ∨ u ∉ freeVarsFormula A := by
    right
    intro hu
    exact freshVar_not_mem_allVars_left comp r.toOption (.all x A) .bot x.ty
      (List.mem_cons_of_mem x (mem_freeVarsFormula_allVars hu))
  have huR : ∀ f ∈ r.toOption, u ∉ freeVars f := by
    intro f hf huf
    have hm := mem_freeVarOccurrences_of_mem_allVars (mem_eraseDups_iff.mp huf)
    have heq : r.toOption = some f := hf
    apply freshVar_not_mem_realizer comp f (.all x A) .bot x.ty
    simpa only [u, heq] using hm
  have e := mr_all_inst_to_common ν comp x A
    (fun C _ ↦ mrFormula_transport_laws ν comp C) r u t huA huR
    (.inr (freshVar_not_free_compBody comp r.toOption (.all x A) .bot x.ty))
  rw [mrFormula_all_apply ν comp x A r]
  exact Provable.conv (Provable.imp_all_elim u t ht hP)
    ((hP.all u).imp hQ) (.imp (.refl _) e)

namespace Induction41

open ComputationalLogic

/-- Introduction of an implication under a finite formula context. -/
theorem ctx_mr_imp_intro (ν : Ty) (comp : CompTerm ν) (Γ : List Formula)
    (A B : Formula) (r : Realizer (tau ν (.imp A B)))
    (hΓ : ∀ C ∈ Γ, SysConfig.Z.allowsFormula C)
    (hA : FormulaWellTyped A) (hB : FormulaWellTyped B) (hr : r.Typed)
    (h : ∀ a : Realizer (tau ν A), a.Typed →
      Provable SysConfig.Z (Formula.impMany (Γ ++ [mrFormula ν comp A a])
        (mrFormula ν comp B (Realizer.applyImp ν A B r a)))) :
    Provable SysConfig.Z (Formula.impMany Γ (mrFormula ν comp (.imp A B) r)) := by
  cases hτ : tau ν A with
  | none =>
      let a : Realizer (tau ν A) := Realizer.cast hτ.symm ()
      rw [mrFormula_imp_none ν comp A B hτ r a]
      simpa only [impMany_append, Formula.impMany] using
        h a ((Realizer.typed_cast _ _).mpr True.intro)
  | some ρ =>
      let xs := freeVarsFormula A ++ freeVarsFormula B ++ freeVarsFormula comp.body ++
        Γ.flatMap freeVarsFormula ++ r.toOption.toList.flatMap freeVars
      obtain ⟨z, hzTy, hz⟩ := FormulaConversion.exists_fresh_var xs ρ
      have hzA : z ∉ freeVarsFormula A := by
        intro hm; apply hz; simp only [xs, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl hm)))
      have hzB : z ∉ freeVarsFormula B := by
        intro hm; apply hz; simp only [xs, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr hm)))
      have hzC : z ∉ freeVarsFormula comp.body := by
        intro hm; apply hz; simp only [xs, List.mem_append]; exact Or.inl (Or.inl (Or.inr hm))
      have hzΓ : ∀ C ∈ Γ, z ∉ freeVarsFormula C := by
        intro C hC hm; apply hz; simp only [xs, List.mem_append]
        exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨C, hC, hm⟩))
      have hzR : ∀ f ∈ r.toOption, z ∉ freeVars f := by
        intro f hf hm; apply hz; simp only [xs, List.mem_append]
        exact Or.inr (List.mem_flatMap.mpr ⟨f, by simpa using hf, hm⟩)
      let a : Realizer (tau ν A) := Realizer.cast hτ.symm (.var z)
      have ha : a.Typed := (Realizer.typed_cast _ _).mpr (by
        change HasType (.var z) ρ
        simpa only [hzTy] using HasType.var z)
      have hBody : Provable SysConfig.Z (Formula.impMany Γ
          (.imp (mrFormula ν comp A a)
            (mrFormula ν comp B (Realizer.applyImp ν A B r a)))) := by
        simpa only [impMany_append, Formula.impMany] using h a ha
      have hAnte := MrLogic.mr_allowed ν comp A a hA ha
      have hCons := MrLogic.mr_allowed ν comp B (Realizer.applyImp ν A B r a) hB
        (Realizer.applyImp_typed ν A B r a hr ha)
      have hAll := ctx_allMany_intro Γ [z] _ hΓ (hAnte.imp hCons)
        (by intro y hy; simp only [List.mem_singleton] at hy; subst y; exact hzΓ) hBody
      exact ctx_conv hΓ (MrLogic.mr_allowed ν comp (.imp A B) r (.imp hA hB) hr)
        (mr_imp_fresh ν comp A B (mrFormula_transport_laws ν comp A)
          (mrFormula_transport_laws ν comp B) ρ hτ r z hzTy hzA hzB hzR (.inr hzC)).symm hAll

/-- A fresh induction index avoiding all formulas and realizers supplied to the proof. -/
theorem fresh_index (ρ : Ty) (Fs : List Formula) (rs : List (Option Term)) :
    ∃ k : Var, k.ty = ρ ∧
      (∀ F ∈ Fs, k ∉ freeVarsFormula F) ∧
      (∀ r ∈ rs, ∀ t ∈ r, k ∉ freeVars t) := by
  obtain ⟨k, hk, hf⟩ := FormulaConversion.exists_fresh_var
    (Fs.flatMap freeVarsFormula ++ rs.flatMap (fun r ↦ r.toList.flatMap freeVars)) ρ
  refine ⟨k, hk, ?_, ?_⟩
  · intro F hF hmem
    exact hf (List.mem_append_left _ (List.mem_flatMap.mpr ⟨F, hF, hmem⟩))
  · intro r hr t ht hmem
    apply hf
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨r, hr, List.mem_flatMap.mpr ⟨t, by simpa using ht, hmem⟩⟩

/-- The step realizer instantiated at an arbitrary object term. -/
def natStepAt (ν : Ty) (n : Var) (A : Formula)
    (b : Realizer (tau ν (.all n (.imp A (substFormula A n (Term.succTerm (.var n)))))))
    (t : Term) : Realizer (tau ν
      (.imp (substFormula A n t) (substFormula A n (Term.succTerm t)))) :=
  Realizer.cast (by simp only [tau_substFormula, tau])
    (Realizer.applyAll ν n (.imp A (substFormula A n (Term.succTerm (.var n)))) b t)

theorem natStepAt_toOption (ν : Ty) (n : Var) (A : Formula)
    (b : Realizer (tau ν (.all n (.imp A (substFormula A n (Term.succTerm (.var n)))))))
    (t : Term) : (natStepAt ν n A b t).toOption = b.toOption.map (fun f ↦ Term.app f t) := by
  simp only [natStepAt, Realizer.toOption_cast, Realizer.applyAll_toOption]

theorem natStepAt_typed (ν : Ty) (n : Var) (A : Formula)
    (b : Realizer (tau ν (.all n (.imp A (substFormula A n (Term.succTerm (.var n)))))))
    (t : Term) (hb : b.Typed) (ht : HasType t n.ty) : (natStepAt ν n A b t).Typed :=
  (Realizer.typed_cast _ _).mpr
    (Realizer.applyAll_typed ν n (.imp A (substFormula A n (Term.succTerm (.var n)))) b t hb ht)

theorem nat_step_source (n : Var) (A : Formula) (t : Term) :
    FormulaBetaREq (substFormula (.imp A (substFormula A n (Term.succTerm (.var n)))) n t)
      (.imp (substFormula A n t) (substFormula A n (Term.succTerm t))) := by
  simp only [substFormula_imp]
  apply FormulaBetaREq.imp (.refl _)
  have h := FormulaConversion.subst_formula_comprehension A n n
    (Term.succTerm (.var n)) t (.inl rfl)
  simpa only [Term.succTerm, substTerm, beq_self_eq_true, ↓reduceIte] using h

theorem nat_step_elim (ν : Ty) (comp : CompTerm ν) (n : Var) (A : Formula)
    (b : Realizer (tau ν (.all n (.imp A (substFormula A n (Term.succTerm (.var n)))))))
    (t : Term) (hn : n.ty = .iota) (hA : FormulaWellTyped A)
    (hb : b.Typed) (ht : HasType t n.ty) :
    Provable SysConfig.Z
      (.imp (mrFormula ν comp (.all n (.imp A (substFormula A n (Term.succTerm (.var n))))) b)
        (mrFormula ν comp (.imp (substFormula A n t) (substFormula A n (Term.succTerm t)))
          (natStepAt ν n A b t))) := by
  have hsn : HasType (Term.succTerm (.var n)) n.ty :=
    hn.symm ▸ HasType.app (.const .succ) (hn ▸ HasType.var n)
  have hst : HasType (Term.succTerm t) n.ty :=
    hn.symm ▸ HasType.app (.const .succ) (hn ▸ ht)
  have hS := FormulaWellTyped.imp hA (hA.substFormula n hsn)
  have hT := FormulaWellTyped.imp (hA.substFormula n ht) (hA.substFormula n hst)
  have hIn := MrLogic.mr_allowed ν comp (.all n _) b (.all n hS) hb
  have hOut := MrLogic.mr_allowed ν comp _ (natStepAt ν n A b t) hT
    (natStepAt_typed ν n A b t hb ht)
  apply Provable.conv (mr_all_elim ν comp n _ b t ht hS hb) (hIn.imp hOut)
  apply FormulaBetaREq.imp (.refl _)
  apply mrFormula_congr ν comp _ _ _ _ (nat_step_source n A t)
  rw [natStepAt_toOption, Realizer.applyAll_toOption]
  cases b.toOption <;> simp only [Option.map_none, Option.map_some]
  · exact .none
  · exact .some (.refl _)

theorem nat_core (ν : Ty) (comp : CompTerm ν) (n : Var) (A : Formula)
    (a : Realizer (tau ν (substFormula A n (.const .zero))))
    (b : Realizer (tau ν (.all n (.imp A (substFormula A n (Term.succTerm (.var n)))))))
    (r : Realizer (tau ν (.all n A)))
    (hn : n.ty = .iota) (hA : FormulaWellTyped A) (ha : a.Typed) (hb : b.Typed)
    (hr : r.Typed)
    (hzero : Option.Rel BetaREq (Realizer.applyAll ν n A r (.const .zero)).toOption a.toOption)
    (hsucc : ∀ t : Term,
      Option.Rel BetaREq (Realizer.applyAll ν n A r (Term.succTerm t)).toOption
        (Realizer.applyImp ν (substFormula A n t) (substFormula A n (Term.succTerm t))
          (natStepAt ν n A b t) (Realizer.applyAll ν n A r t)).toOption) :
    Provable SysConfig.Z (Formula.impMany
      [mrFormula ν comp (substFormula A n (.const .zero)) a,
       mrFormula ν comp (.all n (.imp A (substFormula A n (Term.succTerm (.var n))))) b]
      (mrFormula ν comp (.all n A) r)) := by
  let Z := substFormula A n (.const .zero)
  let S := Formula.all n (.imp A (substFormula A n (Term.succTerm (.var n))))
  have hz : HasType (.const .zero) n.ty := hn.symm ▸ HasType.const .zero
  have hsn : HasType (Term.succTerm (.var n)) n.ty :=
    hn.symm ▸ HasType.app (.const .succ) (hn ▸ HasType.var n)
  have hZ := MrLogic.mr_allowed ν comp Z a (hA.substFormula n hz) ha
  have hS := MrLogic.mr_allowed ν comp S b (.all n (.imp hA (hA.substFormula n hsn))) hb
  let Γ := [mrFormula ν comp Z a, mrFormula ν comp S b]
  have hΓ : ∀ C ∈ Γ, SysConfig.Z.allowsFormula C := by
    intro C hC
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl <;> assumption
  obtain ⟨k, hkn, hkFs, hkRs⟩ :=
    fresh_index n.ty [A, Z, S, comp.body] [r.toOption, a.toOption, b.toOption]
  have hkA : k ∉ freeVarsFormula A := hkFs A (by simp)
  have hkC : k ∉ freeVarsFormula comp.body := hkFs comp.body (by simp)
  have hkR : ∀ t ∈ r.toOption, k ∉ freeVars t := hkRs r.toOption (by simp)
  have hkΓ : ∀ C ∈ Γ, k ∉ freeVarsFormula C := by
    intro C hC
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · exact mrFormula_not_free ν comp Z a k (hkFs Z (by simp))
        (hkRs a.toOption (by simp)) (.inr hkC)
    · exact mrFormula_not_free ν comp S b k (hkFs S (by simp))
        (hkRs b.toOption (by simp)) (.inr hkC)
  have hkt : HasType (.var k) n.ty := hkn ▸ HasType.var k
  have hsk : HasType (Term.succTerm (.var k)) n.ty :=
    hn.symm ▸ HasType.app (.const .succ) (hn ▸ hkt)
  let Ak := substFormula A n (.var k)
  let Ask := substFormula A n (Term.succTerm (.var k))
  let pk := Realizer.applyAll ν n A r (.var k)
  let bk := natStepAt ν n A b (.var k)
  let qk := Realizer.applyImp ν Ak Ask bk pk
  let P := mrFormula ν comp Ak pk
  let Q := mrFormula ν comp Ask qk
  have hAk : FormulaWellTyped Ak := hA.substFormula n hkt
  have hAsk : FormulaWellTyped Ask := hA.substFormula n hsk
  have hpk : pk.Typed := Realizer.applyAll_typed ν n A r (.var k) hr hkt
  have hbk : bk.Typed := natStepAt_typed ν n A b (.var k) hb hkt
  have hqk : qk.Typed := Realizer.applyImp_typed ν Ak Ask bk pk hbk hpk
  have hP := MrLogic.mr_allowed ν comp Ak pk hAk hpk
  have hQ := MrLogic.mr_allowed ν comp Ask qk hAsk hqk
  have hBk := MrLogic.mr_allowed ν comp (.imp Ak Ask) bk (.imp hAk hAsk) hbk
  have ez : FormulaBetaREq (substFormula P k (.const .zero)) (mrFormula ν comp Z a) :=
    (mr_all_inst_to_common ν comp n A (fun C _ ↦ mrFormula_transport_laws ν comp C)
      r k (.const .zero) (.inr hkA) hkR (.inr hkC)).trans
      (mrFormula_congr ν comp Z Z _ a (.refl Z) hzero)
  have es : FormulaBetaREq (substFormula P k (Term.succTerm (.var k))) Q :=
    (mr_all_inst_to_common ν comp n A (fun C _ ↦ mrFormula_transport_laws ν comp C)
      r k (Term.succTerm (.var k)) (.inr hkA) hkR (.inr hkC)).trans
      (mrFormula_congr ν comp Ask Ask _ qk (.refl Ask) (hsucc (.var k)))
  have hPz := hP.substFormula k (hkn.symm ▸ hz)
  have hPs := hP.substFormula k (hkn.symm ▸ hsk)
  have bz : Provable SysConfig.Z (Formula.impMany Γ (substFormula P k (.const .zero))) :=
    ctx_conv hΓ hPz ez.symm (Provable.ctx_hyp hΓ (by simp [Γ]))
  have bstep : Provable SysConfig.Z (Formula.impMany Γ (mrFormula ν comp (.imp Ak Ask) bk)) :=
    Provable.ctx_mp hΓ hS hBk
      (Provable.ctx_const hΓ (nat_step_elim ν comp n A b (.var k) hn hA hb hkt))
      (Provable.ctx_hyp hΓ (by simp [Γ]))
  have bimp : Provable SysConfig.Z (Formula.impMany Γ (.imp P Q)) :=
    Provable.ctx_mp hΓ hBk (hP.imp hQ)
      (Provable.ctx_const hΓ (MrLogic.mr_imp_elim ν comp
        (mrFormula_compatible ν comp) (mrFormula_substitution ν comp)
        Ak Ask bk pk hAk hAsk hbk hpk)) bstep
  have bs : Provable SysConfig.Z (Formula.impMany Γ
      (.all k (.imp P (substFormula P k (Term.succTerm (.var k)))))) := by
    apply ctx_allMany_intro Γ [k] _ hΓ (hP.imp hPs)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst j; exact hkΓ)
    exact ctx_conv hΓ (hP.imp hPs) (.imp (.refl P) es.symm) bimp
  have hind : Provable SysConfig.Z (indNatFormula k P) :=
    ⟨.indNat k P, .indNat k P (hkn.trans hn) hP, rfl⟩
  have hall : Provable SysConfig.Z (Formula.impMany Γ (.all k P)) :=
    Provable.ctx_mp hΓ ((hP.imp hPs).all k) (hP.all k)
      (Provable.ctx_mp hΓ hPz (((hP.imp hPs).all k).imp (hP.all k))
        (Provable.ctx_const hΓ hind) bz) bs
  apply ctx_conv hΓ (MrLogic.mr_allowed ν comp (.all n A) r (.all n hA) hr) _ hall
  apply FormulaBetaREq.symm
  apply mr_all_fresh ν comp n A (fun C _ ↦ mrFormula_transport_laws ν comp C) r k hkn
  · intro hm; exact hkA (List.mem_filter.mp hm).1
  · exact hkR
  · exact .inr hkC

theorem bool_core (ν : Ty) (comp : CompTerm ν) (p : Var) (A : Formula)
    (a : Realizer (tau ν (substFormula A p (.const .trueConst))))
    (b : Realizer (tau ν (substFormula A p (.const .falseConst))))
    (r : Realizer (tau ν (.all p A)))
    (hp : p.ty = .bool) (hA : FormulaWellTyped A) (ha : a.Typed) (hb : b.Typed)
    (hr : r.Typed)
    (htrue : Option.Rel BetaREq (Realizer.applyAll ν p A r (.const .trueConst)).toOption
      a.toOption)
    (hfalse : Option.Rel BetaREq (Realizer.applyAll ν p A r (.const .falseConst)).toOption
      b.toOption) :
    Provable SysConfig.Z (Formula.impMany
      [mrFormula ν comp (substFormula A p (.const .trueConst)) a,
       mrFormula ν comp (substFormula A p (.const .falseConst)) b]
      (mrFormula ν comp (.all p A) r)) := by
  let T := substFormula A p (.const .trueConst)
  let F := substFormula A p (.const .falseConst)
  have ht : HasType (.const .trueConst) p.ty := hp.symm ▸ HasType.const .trueConst
  have hf : HasType (.const .falseConst) p.ty := hp.symm ▸ HasType.const .falseConst
  have hT := MrLogic.mr_allowed ν comp T a (hA.substFormula p ht) ha
  have hF := MrLogic.mr_allowed ν comp F b (hA.substFormula p hf) hb
  let Γ := [mrFormula ν comp T a, mrFormula ν comp F b]
  have hΓ : ∀ C ∈ Γ, SysConfig.Z.allowsFormula C := by
    intro C hC
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl <;> assumption
  obtain ⟨k, hkp, hkFs, hkRs⟩ := fresh_index p.ty [A, comp.body] [r.toOption]
  have hkA : k ∉ freeVarsFormula A := hkFs A (by simp)
  have hkC : k ∉ freeVarsFormula comp.body := hkFs comp.body (by simp)
  have hkR : ∀ t ∈ r.toOption, k ∉ freeVars t := hkRs r.toOption (by simp)
  have hkt : HasType (.var k) p.ty := hkp ▸ HasType.var k
  let P := mrFormula ν comp (substFormula A p (.var k))
    (Realizer.applyAll ν p A r (.var k))
  have hP := MrLogic.mr_allowed ν comp (substFormula A p (.var k))
    (Realizer.applyAll ν p A r (.var k)) (hA.substFormula p hkt)
    (Realizer.applyAll_typed ν p A r (.var k) hr hkt)
  have et : FormulaBetaREq (substFormula P k (.const .trueConst)) (mrFormula ν comp T a) :=
    (mr_all_inst_to_common ν comp p A (fun C _ ↦ mrFormula_transport_laws ν comp C)
      r k (.const .trueConst) (.inr hkA) hkR (.inr hkC)).trans
      (mrFormula_congr ν comp T T _ a (.refl T) htrue)
  have ef : FormulaBetaREq (substFormula P k (.const .falseConst)) (mrFormula ν comp F b) :=
    (mr_all_inst_to_common ν comp p A (fun C _ ↦ mrFormula_transport_laws ν comp C)
      r k (.const .falseConst) (.inr hkA) hkR (.inr hkC)).trans
      (mrFormula_congr ν comp F F _ b (.refl F) hfalse)
  have hpt := hP.substFormula k (hkp.symm ▸ ht)
  have hpf := hP.substFormula k (hkp.symm ▸ hf)
  have bt : Provable SysConfig.Z (Formula.impMany Γ (substFormula P k (.const .trueConst))) :=
    ctx_conv hΓ hpt et.symm (Provable.ctx_hyp hΓ (by simp [Γ]))
  have bf : Provable SysConfig.Z (Formula.impMany Γ (substFormula P k (.const .falseConst))) :=
    ctx_conv hΓ hpf ef.symm (Provable.ctx_hyp hΓ (by simp [Γ]))
  have hind : Provable SysConfig.Z (indBoolFormula k P) :=
    ⟨.indBool k P, .indBool k P (hkp.trans hp) hP, rfl⟩
  have hall : Provable SysConfig.Z (Formula.impMany Γ (.all k P)) :=
    Provable.ctx_mp hΓ hpf (hP.all k)
      (Provable.ctx_mp hΓ hpt (hpf.imp (hP.all k)) (Provable.ctx_const hΓ hind) bt) bf
  apply ctx_conv hΓ (MrLogic.mr_allowed ν comp (.all p A) r (.all p hA) hr) _ hall
  apply FormulaBetaREq.symm
  apply mr_all_fresh ν comp p A (fun C _ ↦ mrFormula_transport_laws ν comp C) r k hkp
  · intro hm; exact hkA (List.mem_filter.mp hm).1
  · exact hkR
  · exact .inr hkC

theorem nat_realizable (ν : Ty) (comp : CompTerm ν) (n : Var) (A : Formula)
    (r : Realizer (tau ν (indNatFormula n A)))
    (hn : n.ty = .iota) (hA : FormulaWellTyped A) (hr : r.Typed)
    (heq : r.toOption = (tau ν A).map (fun ρ ↦ Term.const (.recNat ρ))) :
    Provable SysConfig.Z (mrFormula ν comp (indNatFormula n A) r) := by
  let Z := substFormula A n (.const .zero)
  let S := Formula.all n (.imp A (substFormula A n (Term.succTerm (.var n))))
  let G := Formula.all n A
  have hz : HasType (.const .zero) n.ty := hn.symm ▸ HasType.const .zero
  have hsn : HasType (Term.succTerm (.var n)) n.ty :=
    hn.symm ▸ HasType.app (.const .succ) (hn ▸ HasType.var n)
  have hZ : FormulaWellTyped Z := hA.substFormula n hz
  have hS : FormulaWellTyped S := .all n (.imp hA (hA.substFormula n hsn))
  have hG : FormulaWellTyped G := .all n hA
  apply ctx_mr_imp_intro ν comp [] Z (.imp S G) r (by intro C hC; cases hC)
    hZ (.imp hS hG) hr
  intro a ha
  let r₁ := Realizer.applyImp ν Z (.imp S G) r a
  have hr₁ : r₁.Typed := Realizer.applyImp_typed ν Z (.imp S G) r a hr ha
  apply ctx_mr_imp_intro ν comp [mrFormula ν comp Z a] S G r₁
    (by intro C hC; simp only [List.mem_singleton] at hC; subst C
        exact MrLogic.mr_allowed ν comp Z a hZ ha) hS hG hr₁
  intro b hb
  let r₂ := Realizer.applyImp ν S G r₁ b
  have hr₂ : r₂.Typed := Realizer.applyImp_typed ν S G r₁ b hr₁ hb
  have heqs :
      Option.Rel BetaREq (Realizer.applyAll ν n A r₂ (.const .zero)).toOption a.toOption ∧
      (∀ t : Term,
        Option.Rel BetaREq (Realizer.applyAll ν n A r₂ (Term.succTerm t)).toOption
          (Realizer.applyImp ν (substFormula A n t) (substFormula A n (Term.succTerm t))
            (natStepAt ν n A b t) (Realizer.applyAll ν n A r₂ t)).toOption) := by
    cases hτ : tau ν A with
    | none =>
        have hta : tau ν Z = none := (tau_substFormula ν A n (.const .zero)).trans hτ
        constructor
        · rw [Realizer.toOption_eq_none a hta, Realizer.toOption_eq_none _ hta]
          exact .none
        · intro t
          have htau := (tau_substFormula ν A n (Term.succTerm t)).trans hτ
          rw [Realizer.toOption_eq_none _ htau, Realizer.toOption_eq_none _ htau]
          exact .none
    | some ρ =>
        have hta : tau ν Z = some ρ := (tau_substFormula ν A n (.const .zero)).trans hτ
        have htb : tau ν S = some (.arr .iota (.arr ρ ρ)) := by
          simp only [S, tau, tau_substFormula, hτ, hn]
        have hao := MrLogic.toOption_some a hta
        have hbo := MrLogic.toOption_some b htb
        have ho₁ : r₁.toOption = some (.app (.const (.recNat ρ)) (Realizer.cast hta a)) := by
          have h := Realizer.applyImp_toOption ν Z (.imp S G) r a
          erw [heq, hτ, hao] at h
          exact h
        have ho₂ : r₂.toOption = some
            (.app (.app (.const (.recNat ρ)) (Realizer.cast hta a)) (Realizer.cast htb b)) := by
          have h := Realizer.applyImp_toOption ν S G r₁ b
          rw [ho₁, hbo] at h
          exact h
        constructor
        · rw [Realizer.applyAll_toOption ν n A r₂ (.const .zero), ho₂, hao]
          exact .some (.of_conv (.recNatZero ρ _ _))
        · intro t
          rw [Realizer.applyAll_toOption ν n A r₂ (Term.succTerm t),
            Realizer.applyImp_toOption ν (substFormula A n t)
              (substFormula A n (Term.succTerm t)) (natStepAt ν n A b t)
              (Realizer.applyAll ν n A r₂ t),
            natStepAt_toOption, Realizer.applyAll_toOption ν n A r₂ t, ho₂, hbo]
          exact .some (.of_conv (.recNatSucc ρ _ _ t))
  exact nat_core ν comp n A a b r₂ hn hA ha hb hr₂ heqs.1 heqs.2

theorem bool_realizable (ν : Ty) (comp : CompTerm ν) (p : Var) (A : Formula)
    (r : Realizer (tau ν (indBoolFormula p A)))
    (hp : p.ty = .bool) (hA : FormulaWellTyped A) (hr : r.Typed)
    (heq : r.toOption = (tau ν A).map (fun ρ ↦ Term.const (.recBool ρ))) :
    Provable SysConfig.Z (mrFormula ν comp (indBoolFormula p A) r) := by
  let T := substFormula A p (.const .trueConst)
  let F := substFormula A p (.const .falseConst)
  let G := Formula.all p A
  have ht : HasType (.const .trueConst) p.ty := hp.symm ▸ HasType.const .trueConst
  have hf : HasType (.const .falseConst) p.ty := hp.symm ▸ HasType.const .falseConst
  have hT : FormulaWellTyped T := hA.substFormula p ht
  have hF : FormulaWellTyped F := hA.substFormula p hf
  have hG : FormulaWellTyped G := .all p hA
  apply ctx_mr_imp_intro ν comp [] T (.imp F G) r (by intro C hC; cases hC)
    hT (.imp hF hG) hr
  intro a ha
  let r₁ := Realizer.applyImp ν T (.imp F G) r a
  have hr₁ : r₁.Typed := Realizer.applyImp_typed ν T (.imp F G) r a hr ha
  apply ctx_mr_imp_intro ν comp [mrFormula ν comp T a] F G r₁
    (by intro C hC; simp only [List.mem_singleton] at hC; subst C
        exact MrLogic.mr_allowed ν comp T a hT ha) hF hG hr₁
  intro b hb
  let r₂ := Realizer.applyImp ν F G r₁ b
  have hr₂ : r₂.Typed := Realizer.applyImp_typed ν F G r₁ b hr₁ hb
  have heqs :
      Option.Rel BetaREq (Realizer.applyAll ν p A r₂ (.const .trueConst)).toOption a.toOption ∧
      Option.Rel BetaREq (Realizer.applyAll ν p A r₂ (.const .falseConst)).toOption b.toOption := by
    cases hτ : tau ν A with
    | none =>
        have hta : tau ν T = none := (tau_substFormula ν A p (.const .trueConst)).trans hτ
        have htb : tau ν F = none := (tau_substFormula ν A p (.const .falseConst)).trans hτ
        rw [Realizer.toOption_eq_none a hta, Realizer.toOption_eq_none b htb,
          Realizer.toOption_eq_none _ hta, Realizer.toOption_eq_none _ htb]
        exact ⟨.none, .none⟩
    | some ρ =>
        have hta : tau ν T = some ρ := (tau_substFormula ν A p (.const .trueConst)).trans hτ
        have htb : tau ν F = some ρ := (tau_substFormula ν A p (.const .falseConst)).trans hτ
        have hao := MrLogic.toOption_some a hta
        have hbo := MrLogic.toOption_some b htb
        have ho₁ : r₁.toOption = some (.app (.const (.recBool ρ)) (Realizer.cast hta a)) := by
          have h := Realizer.applyImp_toOption ν T (.imp F G) r a
          erw [heq, hτ, hao] at h
          exact h
        have ho₂ : r₂.toOption = some
            (.app (.app (.const (.recBool ρ)) (Realizer.cast hta a)) (Realizer.cast htb b)) := by
          have h := Realizer.applyImp_toOption ν F G r₁ b
          rw [ho₁, hbo] at h
          exact h
        rw [Realizer.applyAll_toOption ν p A r₂ (.const .trueConst),
          Realizer.applyAll_toOption ν p A r₂ (.const .falseConst), ho₂, hao, hbo]
        exact ⟨.some (.of_conv (.recBoolTrue ρ _ _)),
          .some (.of_conv (.recBoolFalse ρ _ _))⟩
  exact bool_core ν comp p A a b r₂ hp hA ha hb hr₂ heqs.1 heqs.2

end Induction41

/-- The extracted natural recursor realizes the natural-induction axiom. -/
theorem indNat_realizer (ν : Ty) (dummy : Term) (comp : CompTerm ν) (n : Var) (A : Formula)
    (_hd : HasType dummy ν) (_hc : IsClosedTerm dummy)
    (hn : n.ty = .iota) (hA : FormulaWellTyped A) :
    ∃ r : Realizer (tau ν (indNatFormula n A)),
      r.toOption = extractRaw ν dummy (.indNat n A) ∧ r.Typed ∧
      Provable SysConfig.Z (mrFormula ν comp (indNatFormula n A) r) := by
  cases hτ : tau ν A with
  | none =>
      have hi : tau ν (indNatFormula n A) = none := by
        simp only [indNatFormula, tau, tau_substFormula, hτ]
      let r : Realizer (tau ν (indNatFormula n A)) := Realizer.cast hi.symm ()
      have hr : r.Typed := (Realizer.typed_cast _ _).mpr True.intro
      have heq : r.toOption = (tau ν A).map (fun ρ ↦ Term.const (.recNat ρ)) := by
        dsimp only [r]
        erw [Realizer.toOption_cast, hτ]; rfl
      exact ⟨r, heq, hr, Induction41.nat_realizable ν comp n A r hn hA hr heq⟩
  | some ρ =>
      have hi : tau ν (indNatFormula n A) = some (Const.recNat ρ).ty := by
        simp only [indNatFormula, tau, tau_substFormula, hτ, hn, Const.ty]
      let r : Realizer (tau ν (indNatFormula n A)) :=
        Realizer.cast hi.symm (Term.const (.recNat ρ))
      have hr : r.Typed := (Realizer.typed_cast _ _).mpr (HasType.const (.recNat ρ))
      have heq : r.toOption = (tau ν A).map (fun σ ↦ Term.const (.recNat σ)) := by
        dsimp only [r]
        erw [Realizer.toOption_cast, hτ]; rfl
      exact ⟨r, heq, hr, Induction41.nat_realizable ν comp n A r hn hA hr heq⟩

/-- The extracted Boolean recursor realizes the Boolean-induction axiom. -/
theorem indBool_realizer (ν : Ty) (dummy : Term) (comp : CompTerm ν) (p : Var) (A : Formula)
    (_hd : HasType dummy ν) (_hc : IsClosedTerm dummy)
    (hp : p.ty = .bool) (hA : FormulaWellTyped A) :
    ∃ r : Realizer (tau ν (indBoolFormula p A)),
      r.toOption = extractRaw ν dummy (.indBool p A) ∧ r.Typed ∧
      Provable SysConfig.Z (mrFormula ν comp (indBoolFormula p A) r) := by
  cases hτ : tau ν A with
  | none =>
      have hi : tau ν (indBoolFormula p A) = none := by
        simp only [indBoolFormula, tau, tau_substFormula, hτ]
      let r : Realizer (tau ν (indBoolFormula p A)) := Realizer.cast hi.symm ()
      have hr : r.Typed := (Realizer.typed_cast _ _).mpr True.intro
      have heq : r.toOption = (tau ν A).map (fun ρ ↦ Term.const (.recBool ρ)) := by
        dsimp only [r]
        erw [Realizer.toOption_cast, hτ]; rfl
      exact ⟨r, heq, hr, Induction41.bool_realizable ν comp p A r hp hA hr heq⟩
  | some ρ =>
      have hi : tau ν (indBoolFormula p A) = some (Const.recBool ρ).ty := by
        simp only [indBoolFormula, tau, tau_substFormula, hτ, hp, Const.ty]
      let r : Realizer (tau ν (indBoolFormula p A)) :=
        Realizer.cast hi.symm (Term.const (.recBool ρ))
      have hr : r.Typed := (Realizer.typed_cast _ _).mpr (HasType.const (.recBool ρ))
      have heq : r.toOption = (tau ν A).map (fun σ ↦ Term.const (.recBool σ)) := by
        dsimp only [r]
        erw [Realizer.toOption_cast, hτ]; rfl
      exact ⟨r, heq, hr, Induction41.bool_realizable ν comp p A r hp hA hr heq⟩

end BBS2002.V2


/- Local checked proof module: Proof41 -/

namespace BBS2002.V2.Soundness41

open ExtractionTyping41

theorem soundness_separated_of_induction (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    (hNat : ∀ n A, n.ty = .iota → FormulaWellTyped A →
      ∀ r : Realizer (tau ν (indNatFormula n A)),
        r.toOption = extractRaw ν dummy (.indNat n A) → r.Typed →
        Provable SysConfig.Z (mrFormula ν comp (indNatFormula n A) r))
    (hBool : ∀ p A, p.ty = .bool → FormulaWellTyped A →
      ∀ r : Realizer (tau ν (indBoolFormula p A)),
        r.toOption = extractRaw ν dummy (.indBool p A) → r.Typed →
        Provable SysConfig.Z (mrFormula ν comp (indBoolFormula p A) r))
    {M : ProofTerm} {B : Formula} (hDeriv : Derivable SysConfig.ZX M B)
    (hAdm : AdmissibleForExtraction ν dummy M) (hFresh : FreshComp ν comp M)
    (r : Realizer (tau ν B)) (hr : r.toOption = extractRaw ν dummy M) (ht : r.Typed) :
    ContextDerivable (extractionContext ν comp M) (mrFormula ν comp B r) := by
  induction hDeriv with
  | assump u hA =>
      have heq : r = assumpRealizer ν u := Realizer.eq_of_toOption_eq _ _
        (hr.trans (assumpRealizer_toOption ν u).symm)
      subst r
      exact ContextDerivable.hyp (MrLogic.mr_allowed ν comp u.formula _ hA.1 ht)
        ⟨u, List.mem_singleton_self _, rfl⟩
  | indNat n A hn hA => exact .closed (hNat n A hn hA.1 r hr ht)
  | indBool p A hp hA => exact .closed (hBool p A hp hA.1 r hr ht)
  | axTrue => exact .closed (EasyAxioms41.axTrue_realizes ν comp r)
  | axFalse A hA => exact .closed (EasyAxioms41.axFalse_realizes ν comp A hA.1 r ht)
  | efq A _ hA => exact .closed (EasyAxioms41.efq_realizes ν comp A hA.1 r ht)
  | @lamAssump u M B hA hM ih =>
      have hAM : ∀ v ∈ allAssumpVars M, v ∈ allAssumpVars (.lamAssump u M) :=
        fun v hv ↦ List.mem_cons_of_mem u hv
      have hOM : ∀ x ∈ allVarsProof M, x ∈ allVarsProof (.lamAssump u M) :=
        fun x hx ↦ List.mem_append_right _ hx
      have hAdmM := admissible_mono ν dummy hAdm hAM hOM
      have hFreshM := freshComp_mono ν comp hFresh hAM hOM
      obtain ⟨b, hb, hbt⟩ := extractRaw_typed ν dummy hAdm.1 hM
      have hBody := ih hAdmM hFreshM b hb hbt
      have hIntro : ContextDerivable (extractionContext ν comp (.lamAssump u M))
          (.imp (mrFormula ν comp u.formula (assumpRealizer ν u)) (mrFormula ν comp B b)) := by
        apply ContextDerivable.imp_intro
          (MrLogic.mr_allowed ν comp u.formula _ hA.1 (assumpRealizer_typed ν u))
        apply hBody.mono
        intro D ⟨v, hv, heq⟩
        by_cases hvu : v = u
        · subst v
          exact .inl heq
        · exact .inr ⟨v, mem_freeAssumpVars_lamAssump.mpr ⟨hv, hvu⟩, heq⟩
      have hMR := mr_imp_lam ν comp u B r b (by
          rw [hr, extractRaw, ← hb]
          cases tau ν u.formula <;> rfl)
        (by
          intro ρ hx
          apply hAdm.2.2.1 u (List.mem_cons_self ..) ⟨u.id, ρ⟩
            (List.mem_append_left _ (mem_freeVarsFormula_allVars hx))
          rfl)
        (by
          intro ρ t
          apply SemanticSupport41.derivable_subst_invariant hM ⟨u.id, ρ⟩ t
          intro hx
          exact hAdm.2.2.1 u (List.mem_cons_self ..) ⟨u.id, ρ⟩ (hOM _ hx) rfl)
        (hFresh.2 u (List.mem_cons_self ..))
      have hOut := MrLogic.mr_allowed ν comp (.imp u.formula B) r
        (.imp hA.1 (derivable_allowed hM).1) ht
      cases hτ : tau ν u.formula with
      | none =>
          exact hIntro.conv hOut (by simpa only [hτ] using hMR.symm)
      | some ρ =>
          exact (hIntro.all_intro ⟨u.id, ρ⟩
            (extractionContext_assump_fresh ν dummy comp u ρ hAdm hFresh)).conv hOut
            (by simpa only [hτ] using hMR.symm)
  | @appAssump M N A B hM hN ihM ihN =>
      have hAM : ∀ u ∈ allAssumpVars M, u ∈ allAssumpVars (.appAssump M N) :=
        fun u hu ↦ List.mem_append_left _ hu
      have hAN : ∀ u ∈ allAssumpVars N, u ∈ allAssumpVars (.appAssump M N) :=
        fun u hu ↦ List.mem_append_right _ hu
      have hOM : ∀ x ∈ allVarsProof M, x ∈ allVarsProof (.appAssump M N) :=
        fun x hx ↦ List.mem_append_left _ hx
      have hON : ∀ x ∈ allVarsProof N, x ∈ allVarsProof (.appAssump M N) :=
        fun x hx ↦ List.mem_append_right _ hx
      obtain ⟨m, hm, hmt⟩ := extractRaw_typed ν dummy hAdm.1 hM
      obtain ⟨n, hn, hnt⟩ := extractRaw_typed ν dummy hAdm.1 hN
      have hIM := (ihM (admissible_mono ν dummy hAdm hAM hOM)
        (freshComp_mono ν comp hFresh hAM hOM) m hm hmt).mono
        (extractionContext_mono ν comp (N := .appAssump M N) (fun u hu ↦
          mem_freeAssumpVars_appAssump.mpr (.inl hu)))
      have hIN := (ihN (admissible_mono ν dummy hAdm hAN hON)
        (freshComp_mono ν comp hFresh hAN hON) n hn hnt).mono
        (extractionContext_mono ν comp (N := .appAssump M N) (fun u hu ↦
          mem_freeAssumpVars_appAssump.mpr (.inr hu)))
      have hA : FormulaWellTyped A := (derivable_allowed hN).1
      have hB : FormulaWellTyped B := by
        cases (derivable_allowed hM).1 with | imp _ hB => exact hB
      have hApply := (ContextDerivable.closed (Γ := extractionContext ν comp (.appAssump M N))
        (MrLogic.mr_imp_elim ν comp (mrFormula_compatible ν comp) (mrFormula_substitution ν comp)
          A B m n hA hB hmt hnt)).mp hIM |>.mp hIN
      have heq : Realizer.applyImp ν A B m n = r := Realizer.eq_of_toOption_eq _ _ (by
        rw [Realizer.applyImp_toOption, hm, hn, hr]
        rfl)
      simpa only [heq] using hApply
  | @lamTerm x M A hSide hM ih =>
      have hAM : ∀ u ∈ allAssumpVars M, u ∈ allAssumpVars (.lamTerm x M) := fun _ hu ↦ hu
      have hOM : ∀ y ∈ allVarsProof M, y ∈ allVarsProof (.lamTerm x M) :=
        fun y hy ↦ List.mem_cons_of_mem x hy
      obtain ⟨a, ha, hat⟩ := extractRaw_typed ν dummy hAdm.1 hM
      have hIA := ih (admissible_mono ν dummy hAdm hAM hOM)
        (freshComp_mono ν comp hFresh hAM hOM) a ha hat
      have hAll := hIA.all_intro x (extractionContext_object_fresh ν dummy comp x hAdm hFresh hSide)
      have heq := mr_all_lam ν comp x A r a
        (by simpa only [extractRaw, ← ha] using hr) (hFresh.1 x (List.mem_cons_self ..))
      exact hAll.conv (MrLogic.mr_allowed ν comp (.all x A) r
        (.all x (derivable_allowed hM).1) ht) heq.symm
  | @appTerm M x A t hT hM ih =>
      have hAM : ∀ u ∈ allAssumpVars M, u ∈ allAssumpVars (.appTerm M t) := fun _ hu ↦ hu
      have hOM : ∀ y ∈ allVarsProof M, y ∈ allVarsProof (.appTerm M t) :=
        fun y hy ↦ List.mem_append_left _ hy
      obtain ⟨a, ha, hat⟩ := extractRaw_typed ν dummy hAdm.1 hM
      have hIA := ih (admissible_mono ν dummy hAdm hAM hOM)
        (freshComp_mono ν comp hFresh hAM hOM) a ha hat
      have hA : FormulaWellTyped A := by cases (derivable_allowed hM).1 with | all _ hA => exact hA
      have hApply := (ContextDerivable.closed (Γ := extractionContext ν comp (.appTerm M t))
        (mr_all_elim ν comp x A a t hT hA hat)).mp hIA
      have heq : Realizer.applyAll ν x A a t = r := Realizer.eq_of_toOption_eq _ _ (by
        rw [Realizer.applyAll_toOption, ha, hr]
        rfl)
      simpa only [heq] using hApply
  | @conv M A B hM hB hAB ih =>
      let a : Realizer (tau ν A) := Realizer.cast (tau_formulaBetaREq ν hAB).symm r
      have ha : a.toOption = extractRaw ν dummy M :=
        (Realizer.toOption_cast (tau_formulaBetaREq ν hAB).symm r).trans hr
      have hat : a.Typed := (Realizer.typed_cast _ _).mpr ht
      apply (ih hAdm hFresh a ha hat).conv (MrLogic.mr_allowed ν comp B r hB.1 ht)
      apply mrFormula_congr ν comp A B a r hAB
      rw [show a.toOption = r.toOption from Realizer.toOption_cast _ r]
      exact Realizer.toOption_rel_refl r

theorem soundness_separated (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    {M : ProofTerm} {B : Formula} (hDeriv : Derivable SysConfig.ZX M B)
    (hAdm : AdmissibleForExtraction ν dummy M) (hFresh : FreshComp ν comp M)
    (r : Realizer (tau ν B)) (hr : r.toOption = extractRaw ν dummy M) (ht : r.Typed) :
    ContextDerivable (extractionContext ν comp M) (mrFormula ν comp B r) := by
  apply soundness_separated_of_induction ν dummy comp ?_ ?_ hDeriv hAdm hFresh r hr ht
  · intro n A hn hA a ha _
    obtain ⟨s, hs, _, hS⟩ := indNat_realizer ν dummy comp n A hAdm.1 hAdm.2.1 hn hA
    have heq : s = a := Realizer.eq_of_toOption_eq _ _ (hs.trans ha.symm)
    simpa only [heq] using hS
  · intro p A hp hA a ha _
    obtain ⟨s, hs, _, hS⟩ := indBool_realizer ν dummy comp p A hAdm.1 hAdm.2.1 hp hA
    have heq : s = a := Realizer.eq_of_toOption_eq _ _ (hs.trans ha.symm)
    simpa only [heq] using hS

end BBS2002.V2.Soundness41


/- Local checked proof module: Soundness41Closure -/

namespace BBS2002.V2.Soundness41

namespace ContextDerivable

theorem impMany_intro (As : List Formula) {Γ : Formula → Prop} {B : Formula}
    (hAs : ∀ A ∈ As, SysConfig.Z.allowsFormula A)
    (h : ContextDerivable (fun D ↦ D ∈ As ∨ Γ D) B) :
    ContextDerivable Γ (Formula.impMany As B) := by
  induction As generalizing Γ with
  | nil => exact h.mono (fun D hD ↦ hD.resolve_left (List.not_mem_nil))
  | cons A As ih =>
      apply ContextDerivable.imp_intro (hAs A (List.mem_cons_self ..))
      apply ih (fun D hD ↦ hAs D (List.mem_cons_of_mem A hD))
      apply h.mono
      intro D hD
      rcases hD with hD | hD
      · rcases List.mem_cons.mp hD with hDA | hD
        · exact .inr (.inl hDA)
        · exact .inl hD
      · exact .inr (.inr hD)

theorem impMany_elim (As : List Formula) {Γ : Formula → Prop} {B : Formula}
    (h : ContextDerivable Γ (Formula.impMany As B))
    (hAs : ∀ A ∈ As, ContextDerivable Γ A) : ContextDerivable Γ B := by
  induction As with
  | nil => exact h
  | cons A As ih =>
      exact ih (h.mp (hAs A (List.mem_cons_self ..)))
        (fun D hD ↦ hAs D (List.mem_cons_of_mem A hD))

theorem to_provable (As : List Formula) {B : Formula}
    (hAs : ∀ A ∈ As, SysConfig.Z.allowsFormula A)
    (h : ContextDerivable (fun D ↦ D ∈ As) B) :
    Provable SysConfig.Z (Formula.impMany As B) := by
  have h' : ContextDerivable (fun _ ↦ False) (Formula.impMany As B) :=
    impMany_intro As hAs (h.mono (fun _ hD ↦ .inl hD))
  obtain ⟨N, hN, hNf⟩ := h'
  exact ⟨N, hN, List.eq_nil_iff_forall_not_mem.mpr hNf⟩

theorem of_provable (As : List Formula) {B : Formula}
    (hAs : ∀ A ∈ As, SysConfig.Z.allowsFormula A)
    (h : Provable SysConfig.Z (Formula.impMany As B)) :
    ContextDerivable (fun D ↦ D ∈ As) B :=
  impMany_elim As (.closed h) (fun A hA ↦ .hyp (hAs A hA) hA)

end ContextDerivable

/-- Substitution into a closed derivation uses universal introduction and elimination. -/
theorem provable_subst {sys : SysConfig} {A : Formula} (x : Var) (t : Term)
    (ht : HasType t x.ty) (h : Provable sys A) : Provable sys (substFormula A x t) := by
  obtain ⟨N, hN, hNf⟩ := h
  refine ⟨.appTerm (.lamTerm x N) t, .appTerm t ht (.lamTerm x ?_ hN), hNf⟩
  intro u hu
  rw [hNf] at hu
  cases hu

theorem freeAssump_allowed {sys : SysConfig} {M : ProofTerm} {A : Formula}
    (h : Derivable sys M A) {u : AssumpVar} (hu : u ∈ freeAssumpVars M) :
    sys.allowsFormula u.formula := by
  induction h with
  | assump v hV =>
      have huv : u = v := List.mem_singleton.mp hu
      simpa only [huv] using hV
  | indNat | indBool | axTrue | axFalse | efq => cases hu
  | lamAssump _ _ _ ih => exact ih (List.mem_filter.mp hu).1
  | appAssump _ _ ihM ihN =>
      rcases mem_freeAssumpVars_appAssump.mp hu with hu | hu
      · exact ihM hu
      · exact ihN hu
  | lamTerm _ _ _ ih | appTerm _ _ _ ih => exact ih hu
  | conv _ _ _ ih => exact ih hu

def extractionFormulas (ν : Ty) (comp : CompTerm ν) (M : ProofTerm) : List Formula :=
  (freeAssumpVars M).map (fun u ↦ mrFormula ν comp u.formula (assumpRealizer ν u))

theorem mem_extractionFormulas (ν : Ty) (comp : CompTerm ν) (M : ProofTerm) (D : Formula) :
    D ∈ extractionFormulas ν comp M ↔ extractionContext ν comp M D := by
  constructor
  · intro h
    obtain ⟨u, hu, heq⟩ := List.mem_map.mp h
    exact ⟨u, hu, heq.symm⟩
  · intro ⟨u, hu, heq⟩
    exact List.mem_map.mpr ⟨u, hu, heq.symm⟩

theorem extractionFormulas_allowed (ν : Ty) (comp : CompTerm ν)
    {M : ProofTerm} {A : Formula} (h : Derivable SysConfig.ZX M A) :
    ∀ D ∈ extractionFormulas ν comp M, SysConfig.Z.allowsFormula D := by
  intro D hD
  obtain ⟨u, hu, heq⟩ := (mem_extractionFormulas ν comp M D).mp hD
  rw [heq]
  exact MrLogic.mr_allowed ν comp u.formula (assumpRealizer ν u)
    (freeAssump_allowed h hu).1 (assumpRealizer_typed ν u)

theorem close_extraction (ν : Ty) (comp : CompTerm ν)
    {M : ProofTerm} {A B : Formula} (hM : Derivable SysConfig.ZX M A)
    (h : ContextDerivable (extractionContext ν comp M) B) :
    Provable SysConfig.Z (Formula.impMany (extractionFormulas ν comp M) B) :=
  ContextDerivable.to_provable _ (extractionFormulas_allowed ν comp hM)
    (h.mono (fun D hD ↦ (mem_extractionFormulas ν comp M D).mpr hD))

theorem open_extraction (ν : Ty) (comp : CompTerm ν)
    {M : ProofTerm} {A B : Formula} (hM : Derivable SysConfig.ZX M A)
    (h : Provable SysConfig.Z (Formula.impMany (extractionFormulas ν comp M) B)) :
    ContextDerivable (extractionContext ν comp M) B :=
  (ContextDerivable.of_provable _ (extractionFormulas_allowed ν comp hM) h).mono
    (fun D hD ↦ (mem_extractionFormulas ν comp M D).mp hD)

end BBS2002.V2.Soundness41


/- Local checked proof module: Soundness41Formula -/

namespace BBS2002.V2.Soundness41

theorem subst_impMany_map_congr {α : Type} (xs : List α) (f g : α → Formula)
    (A B : Formula) (x : Var) (t : Term)
    (hfg : ∀ a ∈ xs, FormulaBetaREq (substFormula (f a) x t) (g a))
    (hAB : FormulaBetaREq (substFormula A x t) B) :
    FormulaBetaREq (substFormula (Formula.impMany (xs.map f) A) x t)
      (Formula.impMany (xs.map g) B) := by
  induction xs with
  | nil => exact hAB
  | cons a xs ih =>
      simp only [List.map_cons, Formula.impMany, substFormula_imp]
      exact .imp (hfg a (List.mem_cons_self ..))
        (ih (fun b hb ↦ hfg b (List.mem_cons_of_mem a hb)))

end BBS2002.V2.Soundness41


/- Local checked proof module: CompSubstitution41 -/

namespace BBS2002.V2.CompTransport41

theorem mr_comp_subst_all (ν : Ty) (comp comp' : CompTerm ν) (x : Var) (t : Term)
    (v : Var) (A : Formula)
    (hSmall : ∀ C, formulaSize C < formulaSize (.all v A) →
      ∀ r : Realizer (tau ν C),
      FormulaBetaREq (substFormula (mrFormula ν comp C r) x t)
        (mrFormula ν comp' (substFormula C x t)
          (Realizer.cast (tau_substFormula ν C x t).symm (Realizer.subst r x t))))
    (r : Realizer (tau ν (.all v A))) :
    FormulaBetaREq (substFormula (mrFormula ν comp (.all v A) r) x t)
      (mrFormula ν comp' (substFormula (.all v A) x t)
        (Realizer.cast (tau_substFormula ν (.all v A) x t).symm (Realizer.subst r x t))) := by
  obtain ⟨z, hzTy, hz⟩ := FormulaConversion.exists_fresh_var
    ([x] ++ (allVarsFormula A ++ (allVarsFormula comp.body ++ allVarsFormula comp'.body ++
      (r.toOption.toList.flatMap freeVars ++ freeVars t)))) v.ty
  simp only [List.mem_append, List.mem_singleton, not_or] at hz
  obtain ⟨hzx, hzA, ⟨hzC, hzC'⟩, hzRL, hzt⟩ := hz
  have hzAF : z ∉ freeVarsFormula A := fun h ↦ hzA (mem_freeVarsFormula_allVars h)
  have hzCF : z ∉ freeVarsFormula comp.body := fun h ↦ hzC (mem_freeVarsFormula_allVars h)
  have hzCF' : z ∉ freeVarsFormula comp'.body := fun h ↦ hzC' (mem_freeVarsFormula_allVars h)
  have hzR : ∀ f ∈ r.toOption, z ∉ freeVars f := by
    intro f hf hzf
    exact hzRL (List.mem_flatMap.mpr ⟨f, Option.mem_toList.mpr hf, hzf⟩)
  have hztO : z ∉ freeVarOccurrences t := fun h ↦ hzt (mem_eraseDups_of_mem' _ h)
  let C := substFormula A v (.var z)
  let D := substFormula C x t
  let F := substFormula (.all v A) x t
  let a := Realizer.applyAll ν v A r (.var z)
  let b : Realizer (tau ν D) :=
    Realizer.cast (tau_substFormula ν C x t).symm (Realizer.subst a x t)
  let rs : Realizer (tau ν F) :=
    Realizer.cast (tau_substFormula ν (.all v A) x t).symm (Realizer.subst r x t)
  have hNorm : FormulaBetaREq F (.all z D) :=
    subst_formula_all_fresh A v z x t hzTy.symm hzA hzx hztO
  let s : Realizer (tau ν (.all z D)) := Realizer.cast (tau_formulaBetaREq ν hNorm) rs
  have hSopt : s.toOption = r.toOption.map (fun f ↦ substTerm f x t) :=
    (Realizer.toOption_cast _ _).trans
      ((Realizer.toOption_cast _ _).trans (Realizer.subst_toOption r x t))
  have hBopt : b.toOption =
      (r.toOption.map (fun f ↦ Term.app f (.var z))).map (fun f ↦ substTerm f x t) :=
    (Realizer.toOption_cast _ _).trans
      ((Realizer.subst_toOption a x t).trans
        (congrArg (fun q ↦ q.map (fun f ↦ substTerm f x t))
          (Realizer.applyAll_toOption ν v A r (.var z))))
  have hrP : r.SupportedBy (fun w ↦ w ≠ z) := by
    intro f hf w hw heq
    subst w
    exact hzR f hf hw
  have htP : ∀ w ∈ freeVars t, w ≠ z := by
    intro w hw heq
    subst w
    exact hzt hw
  have hsP : s.SupportedBy (fun w ↦ w ≠ z) := ((hrP.subst x t htP).cast _).cast _
  have hzS : ∀ f ∈ s.toOption, z ∉ freeVars f :=
    fun f hf hzf ↦ hsP f hf z hzf rfl
  have hNormMR : FormulaBetaREq (mrFormula ν comp' F rs)
      (mrFormula ν comp' (.all z D) s) := by
    apply mrFormula_congr ν comp' F (.all z D) rs s hNorm
    rw [show s.toOption = rs.toOption from Realizer.toOption_cast _ _]
    exact Realizer.toOption_rel_refl rs
  have hRightCanon := mr_all_fresh ν comp' z D (fun E _ ↦ mrFormula_transport_laws ν comp' E) s z rfl
    (not_mem_freeVarsFormula_all z D) hzS (.inr hzCF')
  have hRightBody :
      mrFormula ν comp' (substFormula D z (.var z)) (Realizer.applyAll ν z D s (.var z)) =
        mrFormula ν comp' D b := by
    apply mrFormula_source_eq ν comp' (substFormula_var_self D z)
    rw [Realizer.applyAll_toOption, hSopt, hBopt]
    cases r.toOption <;>
      simp only [Option.map_none, Option.map_some, substTerm,
        beq_eq_false_iff_ne.mpr hzx, Bool.false_eq_true, ↓reduceIte]
  have hRight : FormulaBetaREq (mrFormula ν comp' F rs) (.all z (mrFormula ν comp' D b)) := by
    rw [hRightBody] at hRightCanon
    exact hNormMR.trans hRightCanon
  have hLeftCanon := mr_all_fresh ν comp v A (fun E _ ↦ mrFormula_transport_laws ν comp E) r z hzTy
    (fun h ↦ hzAF (List.mem_filter.mp h).1) hzR (.inr hzCF)
  have hLeft := FormulaConversion.subst_formula_congr x hLeftCanon (.refl t)
  have hSubAll :
      substFormula (.all z (mrFormula ν comp C a)) x t =
        .all z (substFormula (mrFormula ν comp C a) x t) := by
    rw [substFormula.eq_def]
    simp only [beq_eq_false_iff_ne.mpr hzx, Bool.false_eq_true, ↓reduceIte, hztO]
  rw [hSubAll] at hLeft
  have hBody := (hSmall C (by
    simp only [C, formulaSize_substFormula, formulaSize]
    omega)) a
  exact hLeft.trans ((FormulaBetaREq.all z hBody).trans hRight.symm)


private theorem formula_transport {A B C D : Formula}
    (hA : A = C) (hB : B = D) (h : FormulaBetaREq C D) : FormulaBetaREq A B := by
  cases hA
  cases hB
  exact h

theorem mr_comp_subst_step (ν : Ty) (comp comp' : CompTerm ν) (x : Var) (t : Term)
    (hApply : ∀ q : Term, FormulaBetaREq (substFormula (comp.apply q) x t)
      (comp'.apply (substTerm q x t))) (A : Formula)
    (hSmall : ∀ C, formulaSize C < formulaSize A →
      ∀ r : Realizer (tau ν C),
      FormulaBetaREq (substFormula (mrFormula ν comp C r) x t)
        (mrFormula ν comp' (substFormula C x t)
          (Realizer.cast (tau_substFormula ν C x t).symm (Realizer.subst r x t))))
    (r : Realizer (tau ν A)) :
    FormulaBetaREq (substFormula (mrFormula ν comp A r) x t)
      (mrFormula ν comp' (substFormula A x t)
        (Realizer.cast (tau_substFormula ν A x t).symm (Realizer.subst r x t))) := by
  match A with
  | .bot =>
      exact formula_transport
        ((congrArg (fun F ↦ substFormula F x t) (mrFormula.eq_def ν comp .bot r)).trans
          (substFormula_bot x t))
        ((mrFormula_source_eq ν comp' (substFormula_bot x t) _ ()
          (by rw [Realizer.toOption_cast, Realizer.subst_toOption]; rfl)).trans
          (mrFormula.eq_def ν comp' .bot ())) .bot
  | .varX =>
      exact formula_transport
        (congrArg (fun F ↦ substFormula F x t) (mrFormula.eq_def ν comp .varX r))
        ((mrFormula_source_eq ν comp' (substFormula_varX x t) _ (substTerm r x t)
          (by rw [Realizer.toOption_cast, Realizer.subst_toOption]; rfl)).trans
          (mrFormula.eq_def ν comp' .varX (substTerm r x t)))
        (hApply r)
  | .atom a =>
      exact formula_transport
        ((congrArg (fun F ↦ substFormula F x t) (mrFormula.eq_def ν comp (.atom a) r)).trans
          (substFormula_atom a x t))
        ((mrFormula_source_eq ν comp' (substFormula_atom a x t) _ ()
          (by rw [Realizer.toOption_cast, Realizer.subst_toOption]; rfl)).trans
          (mrFormula.eq_def ν comp' (.atom (substTerm a x t)) ())) (.refl _)
  | .imp A B =>
      have hA := hSmall A (by simp [formulaSize]; omega)
      have hB := hSmall B (by simp [formulaSize]; omega)
      let rs : Realizer (tau ν (.imp (substFormula A x t) (substFormula B x t))) :=
        Realizer.cast (by simp only [tau, tau_substFormula]) (Realizer.subst r x t)
      have hRS : rs.toOption = (Realizer.subst r x t).toOption := Realizer.toOption_cast _ _
      have hTarget := mrFormula_source_eq ν comp' (substFormula_imp A B x t)
        (Realizer.cast (tau_substFormula ν (.imp A B) x t).symm (Realizer.subst r x t)) rs
        ((Realizer.toOption_cast _ _).trans hRS.symm)
      cases hτA : tau ν A with
      | none =>
          let ar : Realizer (tau ν A) := Realizer.cast hτA.symm ()
          let ar' : Realizer (tau ν (substFormula A x t)) :=
            Realizer.cast (tau_substFormula ν A x t).symm (Realizer.subst ar x t)
          refine formula_transport
            ((congrArg (fun F ↦ substFormula F x t) (mrFormula_imp_none ν comp A B hτA r ar)).trans
              (substFormula_imp _ _ x t))
            (hTarget.trans (mrFormula_imp_none ν comp' _ _
              ((tau_substFormula ν A x t).trans hτA) rs ar')) ?_
          refine .imp (hA ar) ?_
          exact formula_transport rfl
            (mrFormula_source_eq ν comp' rfl _ _
              ((applyImp_subst_toOption ν A B _ _ r ar rs ar' x t hRS
                (Realizer.toOption_cast _ _)).trans (Realizer.toOption_cast _ _).symm))
            (hB (Realizer.applyImp ν A B r ar))
      | some ρ =>
          obtain ⟨z, hzTy, hzF, hzR, hzT, hzX⟩ := exists_fresh_parameters
            [A, B, substFormula A x t, substFormula B x t, comp.body, comp'.body]
            [r.toOption, rs.toOption] [t] [x] ρ
          have hzx : z ≠ x := by simpa only [List.mem_singleton] using hzX
          have hzt : z ∉ freeVarOccurrences t := fun hz ↦
            hzT t (by simp) (mem_eraseDups_of_mem' _ hz)
          have hzComp : z = comp.var ∨ z ∉ freeVarsFormula comp.body :=
            .inr (hzF comp.body (by simp))
          have hzComp' : z = comp'.var ∨ z ∉ freeVarsFormula comp'.body :=
            .inr (hzF comp'.body (by simp))
          let ar : Realizer (tau ν A) := Realizer.cast hτA.symm (Term.var z)
          let ar' : Realizer (tau ν (substFormula A x t)) :=
            Realizer.cast ((tau_substFormula ν A x t).trans hτA).symm (Term.var z)
          have hAR : ar'.toOption = (Realizer.subst ar x t).toOption := by
            have ha : ar.toOption = some (.var z) := Realizer.toOption_cast _ _
            have ha' : ar'.toOption = some (.var z) := Realizer.toOption_cast _ _
            rw [ha', Realizer.subst_toOption, ha]
            simp only [Option.map_some, substTerm, beq_iff_eq, hzx, ↓reduceIte]
          have hLeft := mr_imp_fresh ν comp A B (mrFormula_transport_laws ν comp A) (mrFormula_transport_laws ν comp B) ρ hτA r z hzTy
            (hzF A (by simp)) (hzF B (by simp))
            (hzR r.toOption (by simp)) hzComp
          have hRight := mr_imp_fresh ν comp' (substFormula A x t) (substFormula B x t)
            (mrFormula_transport_laws ν comp' _) (mrFormula_transport_laws ν comp' _) ρ ((tau_substFormula ν A x t).trans hτA) rs z hzTy
            (hzF _ (by simp)) (hzF _ (by simp))
            (hzR rs.toOption (by simp)) hzComp'
          refine (FormulaConversion.subst_formula_congr x hLeft (.refl t)).trans ?_
          refine FormulaBetaREq.trans ?_ (formula_transport hTarget rfl hRight).symm
          have hBinder : substFormula
              (.all z (.imp (mrFormula ν comp A ar)
                (mrFormula ν comp B (Realizer.applyImp ν A B r ar)))) x t =
              .all z (.imp (substFormula (mrFormula ν comp A ar) x t)
                (substFormula (mrFormula ν comp B (Realizer.applyImp ν A B r ar)) x t)) := by
            rw [substFormula.eq_def]
            simp only [beq_iff_eq, hzx, hzt, ↓reduceIte, substFormula_imp]
          refine formula_transport hBinder rfl (.all z (.imp ?_ ?_))
          · exact formula_transport rfl
              (mrFormula_source_eq ν comp' rfl ar' _
                (hAR.trans (Realizer.toOption_cast _ _).symm))
              (hA ar)
          · exact formula_transport rfl
              (mrFormula_source_eq ν comp' rfl _ _
                ((applyImp_subst_toOption ν A B _ _ r ar rs ar' x t hRS hAR).trans
                  (Realizer.toOption_cast _ _).symm))
              (hB (Realizer.applyImp ν A B r ar))
  | .all v A =>
      exact mr_comp_subst_all ν comp comp' x t v A hSmall r

theorem mr_comp_subst (ν : Ty) (comp comp' : CompTerm ν) (x : Var) (t : Term)
    (hApply : ∀ q : Term, FormulaBetaREq (substFormula (comp.apply q) x t)
      (comp'.apply (substTerm q x t))) (A : Formula) (r : Realizer (tau ν A)) :
    FormulaBetaREq (substFormula (mrFormula ν comp A r) x t)
      (mrFormula ν comp' (substFormula A x t)
        (Realizer.cast (tau_substFormula ν A x t).symm (Realizer.subst r x t))) := by
  suffices ∀ n, ∀ A : Formula, formulaSize A = n → ∀ r : Realizer (tau ν A),
      FormulaBetaREq (substFormula (mrFormula ν comp A r) x t)
        (mrFormula ν comp' (substFormula A x t)
          (Realizer.cast (tau_substFormula ν A x t).symm (Realizer.subst r x t))) from
    this (formulaSize A) A rfl r
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro A hEq r
      apply mr_comp_subst_step ν comp comp' x t hApply A _ r
      intro C hC s
      exact ih (formulaSize C) (hEq ▸ hC) C rfl s

theorem mr_comp_subst_fixed (ν : Ty) (comp comp' : CompTerm ν) (x : Var) (t : Term)
    (hApply : ∀ q : Term, FormulaBetaREq (substFormula (comp.apply q) x t)
      (comp'.apply (substTerm q x t))) (A : Formula) (r : Realizer (tau ν A))
    (hA : FormulaBetaREq (substFormula A x t) A)
    (hr : ∀ q ∈ r.toOption, x ∉ freeVars q) :
    FormulaBetaREq (substFormula (mrFormula ν comp A r) x t) (mrFormula ν comp' A r) := by
  refine (mr_comp_subst ν comp comp' x t hApply A r).trans ?_
  apply mrFormula_congr ν comp' _ A _ r hA
  rw [Realizer.toOption_cast, Realizer.subst_toOption]
  cases hOpt : r.toOption with
  | none => exact .none
  | some q =>
      exact .some (.of_alpha (substTerm_alphaEq_of_not_free q x t
        (fun h ↦ hr q hOpt (mem_eraseDups_of_mem' _ h))))

end BBS2002.V2.CompTransport41


/- Local checked proof module: Soundness41Transport -/

namespace BBS2002.V2.Soundness41

/-- Transport the translated conclusion and every translated assumption together
by substituting into their closed, iterated-implication presentation. -/
theorem context_comp_subst (ν : Ty) (comp comp' : CompTerm ν) (x : Var) (t : Term)
    (hApply : ∀ q : Term, FormulaBetaREq (substFormula (comp.apply q) x t)
      (comp'.apply (substTerm q x t)))
    {M : ProofTerm} {B : Formula} (hDeriv : Derivable SysConfig.ZX M B)
    (r : Realizer (tau ν B)) (hr : r.Typed)
    (hB : FormulaBetaREq (substFormula B x t) B)
    (hR : ∀ q ∈ r.toOption, x ∉ freeVars q)
    (hSource : ∀ u ∈ freeAssumpVars M,
      FormulaBetaREq (substFormula u.formula x t) u.formula)
    (hAssump : ∀ u ∈ freeAssumpVars M,
      ∀ q ∈ (assumpRealizer ν u).toOption, x ∉ freeVars q)
    (ht : HasType t x.ty)
    (h : ContextDerivable (extractionContext ν comp M) (mrFormula ν comp B r)) :
    ContextDerivable (extractionContext ν comp' M) (mrFormula ν comp' B r) := by
  apply open_extraction ν comp' hDeriv
  apply Provable.conv (provable_subst x t ht (close_extraction ν comp hDeriv h))
    (SysConfig.allowsFormula.impMany (extractionFormulas_allowed ν comp' hDeriv)
      (MrLogic.mr_allowed ν comp' B r (ExtractionTyping41.derivable_allowed hDeriv).1 hr))
  apply subst_impMany_map_congr (freeAssumpVars M)
    (fun u ↦ mrFormula ν comp u.formula (assumpRealizer ν u))
    (fun u ↦ mrFormula ν comp' u.formula (assumpRealizer ν u))
    (mrFormula ν comp B r) (mrFormula ν comp' B r) x t
  · intro u hu
    exact CompTransport41.mr_comp_subst_fixed ν comp comp' x t hApply
      u.formula (assumpRealizer ν u) (hSource u hu) (hAssump u hu)
  · exact CompTransport41.mr_comp_subst_fixed ν comp comp' x t hApply B r hB hR

/-- The usual fresh-alias hypotheses imply all source invariance obligations in
`context_comp_subst`, including variables introduced only by conversion. -/
theorem context_comp_subst_fresh (ν : Ty) (comp comp' : CompTerm ν) (x : Var) (t : Term)
    (hApply : ∀ q : Term, FormulaBetaREq (substFormula (comp.apply q) x t)
      (comp'.apply (substTerm q x t)))
    {M : ProofTerm} {B : Formula} (hDeriv : Derivable SysConfig.ZX M B)
    (r : Realizer (tau ν B)) (hr : r.Typed)
    (hObj : x ∉ allVarsProof M)
    (hLabels : ∀ u ∈ allAssumpVars M, x.id ≠ u.id)
    (hR : ∀ q ∈ r.toOption, x ∉ freeVars q)
    (ht : HasType t x.ty)
    (h : ContextDerivable (extractionContext ν comp M) (mrFormula ν comp B r)) :
    ContextDerivable (extractionContext ν comp' M) (mrFormula ν comp' B r) := by
  apply context_comp_subst ν comp comp' x t hApply hDeriv r hr
    (SemanticSupport41.derivable_subst_invariant hDeriv x t hObj) hR ?_ ?_ ht h
  · intro u hu
    have hU : Derivable SysConfig.ZX (.assump u) u.formula :=
      .assump u (freeAssump_allowed hDeriv hu)
    apply SemanticSupport41.derivable_subst_invariant hU x t
    exact fun hx ↦ hObj (allAssumpVars_formula_vars (freeAssumpVars_subset_all hu) hx)
  · intro u hu
    exact assumpRealizer_not_free ν u x (hLabels u (freeAssumpVars_subset_all hu))

end BBS2002.V2.Soundness41


/- Local checked proof module: FreshenComp41 -/

namespace BBS2002.V2.Soundness41

private def aliasComp (ν : Ty) (comp : CompTerm ν) (x z : Var)
    (hzTy : z.ty = x.ty) : CompTerm ν where
  var := comp.var
  body := substFormula comp.body x (.var z)
  var_ty := comp.var_ty
  body_isL := (isLFormula_substFormula comp.body x (.var z)).trans comp.body_isL
  body_wt := comp.body_wt.substFormula x (hzTy ▸ HasType.var z)

private theorem aliasComp_apply (ν : Ty) (comp : CompTerm ν) (x z : Var)
    (hzTy : z.ty = x.ty) (hxVar : x ≠ comp.var) (hzVar : z ≠ comp.var)
    (hzBody : z ∉ freeVarsFormula comp.body) (q : Term) :
    FormulaBetaREq (substFormula ((aliasComp ν comp x z hzTy).apply q) z (.var x))
      (comp.apply (substTerm q z (.var x))) := by
  have hBody : FormulaBetaREq
      (substFormula (substFormula comp.body x (.var z)) z (.var x)) comp.body := by
    have h := FormulaConversion.subst_formula_comprehension
      comp.body x z (.var z) (.var x) (.inr hzBody)
    simpa only [substTerm, beq_self_eq_true, ↓reduceIte, substFormula_var_self] using h
  exact (FormulaConversion.subst_formula_compose
    (substFormula comp.body x (.var z)) comp.var z q (.var x) hzVar.symm
    (by simpa only [freeVarOccurrences, List.mem_singleton] using Ne.symm hxVar)).trans
    (FormulaConversion.subst_formula_congr comp.var hBody (.refl _))

private theorem soundness_cover (ν : Ty) (dummy : Term) (M : ProofTerm) (B : Formula)
    (hDeriv : Derivable SysConfig.ZX M B) (hAdm : AdmissibleForExtraction ν dummy M)
    (r : Realizer (tau ν B)) (hr : r.toOption = extractRaw ν dummy M) (ht : r.Typed)
    (xs : List Var) (comp : CompTerm ν)
    (hCover : ∀ w ∈ freeVarsFormula comp.body,
      w = comp.var ∨ w ∈ xs ∨
        (w ∉ allVarsProof M ∧ ∀ u ∈ allAssumpVars M, w.id ≠ u.id)) :
    ContextDerivable (extractionContext ν comp M) (mrFormula ν comp B r) := by
  induction xs generalizing comp with
  | nil =>
      have hFresh : FreshComp ν comp M := by
        constructor
        · intro w hw
          by_cases hEq : w = comp.var
          · exact .inl hEq
          · refine .inr (fun hFree ↦ ?_)
            rcases hCover w hFree with hVar | hList | hGood
            · exact hEq hVar
            · cases hList
            · exact hGood.1 hw
        · intro u hu ρ
          by_cases hEq : (⟨u.id, ρ⟩ : Var) = comp.var
          · exact .inl hEq
          · refine .inr (fun hFree ↦ ?_)
            rcases hCover ⟨u.id, ρ⟩ hFree with hVar | hList | hGood
            · exact hEq hVar
            · cases hList
            · exact hGood.2 u hu rfl
      exact soundness_separated ν dummy comp hDeriv hAdm hFresh r hr ht
  | cons x xs ih =>
      by_cases hxVar : x = comp.var
      · apply ih comp
        intro w hw
        rcases hCover w hw with hVar | hList | hGood
        · exact .inl hVar
        · rcases List.mem_cons.mp hList with hwx | hTail
          · exact .inl (hwx.trans hxVar)
          · exact .inr (.inl hTail)
        · exact .inr (.inr hGood)
      · obtain ⟨z, hzTy, hz⟩ := FormulaConversion.exists_fresh_var
          ([comp.var, x] ++ allVarsProof M ++
            ((allAssumpVars M).map fun u ↦ (⟨u.id, x.ty⟩ : Var)) ++
            freeVarsFormula comp.body ++ freeVarsFormula B ++
            r.toOption.toList.flatMap freeVars) x.ty
        have hzParts : z ≠ comp.var ∧ z ≠ x ∧ z ∉ allVarsProof M ∧
            z ∉ ((allAssumpVars M).map fun u ↦ (⟨u.id, x.ty⟩ : Var)) ∧
            z ∉ freeVarsFormula comp.body ∧ z ∉ freeVarsFormula B ∧
            z ∉ r.toOption.toList.flatMap freeVars := by
          simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
            not_or, and_assoc] using hz
        obtain ⟨hzVar, hzx, hzM, hzIds, hzBody, hzB, hzTerms⟩ := hzParts
        have hzID : ∀ u ∈ allAssumpVars M, z.id ≠ u.id := by
          intro u hu heq
          apply hzIds
          apply List.mem_map.mpr
          refine ⟨u, hu, ?_⟩
          cases z
          simp_all
        let compSafe := aliasComp ν comp x z hzTy
        have hCoverSafe : ∀ w ∈ freeVarsFormula compSafe.body,
            w = compSafe.var ∨ w ∈ xs ∨
              (w ∉ allVarsProof M ∧ ∀ u ∈ allAssumpVars M, w.id ≠ u.id) := by
          intro w hw
          rcases Support.subst_formula_support comp.body x (.var z) w hw with hOld | hAlias
          · rcases hCover w hOld.1 with hVar | hList | hGood
            · exact .inl hVar
            · rcases List.mem_cons.mp hList with hwx | hTail
              · exact False.elim (hOld.2 hwx)
              · exact .inr (.inl hTail)
            · exact .inr (.inr hGood)
          · have hwz : w = z := by
              simpa only [freeVars, freeVarOccurrences, List.mem_eraseDups,
                List.mem_singleton] using hAlias
            subst w
            exact .inr (.inr ⟨hzM, hzID⟩)
        have hSafe := ih compSafe hCoverSafe
        have hzR : ∀ q ∈ r.toOption, z ∉ freeVars q := by
          intro q hq hzq
          exact hzTerms (List.mem_flatMap.mpr ⟨q, Option.mem_toList.mpr hq, hzq⟩)
        exact context_comp_subst_fresh ν compSafe comp z (.var x)
          (aliasComp_apply ν comp x z hzTy hxVar hzVar hzBody)
          hDeriv r ht hzM hzID hzR (hzTy.symm ▸ HasType.var x) hSafe

/-- Soundness for an arbitrary comprehension term, with all its free parameters preserved. -/
theorem soundness (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    {M : ProofTerm} {B : Formula} (hDeriv : Derivable SysConfig.ZX M B)
    (hAdm : AdmissibleForExtraction ν dummy M)
    (r : Realizer (tau ν B)) (hr : r.toOption = extractRaw ν dummy M) (ht : r.Typed) :
    ContextDerivable (extractionContext ν comp M) (mrFormula ν comp B r) :=
  soundness_cover ν dummy M B hDeriv hAdm r hr ht (freeVarsFormula comp.body) comp
    (fun _ hw ↦ .inr (.inl hw))

end BBS2002.V2.Soundness41


/- Local checked proof module: Solution41 -/

open BBS2002 BBS2002.V2

theorem solution
    (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    (M : ProofTerm) (B : Formula)
    (hDeriv : Derivable SysConfig.ZX M B)
    (hAdm : AdmissibleForExtraction ν dummy M) :
    ∃ r : Realizer (tau ν B),
      r.toOption = extractProgram ν dummy M B ∧
      r.Typed ∧
      ∃ N : ProofTerm,
        Derivable SysConfig.Z N (mrFormula ν comp B r) ∧
        ∀ v ∈ freeAssumpVars N,
          ∃ u ∈ freeAssumpVars M,
            v.formula = mrFormula ν comp u.formula (assumpRealizer ν u) := by
  obtain ⟨r, hr, ht⟩ := ExtractionTyping41.extractRaw_typed ν dummy hAdm.1 hDeriv
  refine ⟨r, hr.trans (ExtractionTyping41.extractProgram_eq_extractRaw ν dummy hAdm.1 hDeriv).symm,
    ht, ?_⟩
  exact Soundness41.soundness ν dummy comp hDeriv hAdm r hr ht

