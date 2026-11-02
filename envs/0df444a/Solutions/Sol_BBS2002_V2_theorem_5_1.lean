-- Prove2me | solution 1 for BBS2002.V2.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:32:05.756601+00:00
-- url     : https://prove2.me/submissions/65af0c42-2403-4b84-8bde-d0fe404dbd39

import Definitions.Def_BBS2002_Arithmetic
import Definitions.Def_BBS2002_V2_Realizability
import Theorems.Thm_BBS2002_V2_theorem_4_1

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


/- Local checked proof module: Proof51 -/

namespace BBS2002.V2.ComputationalReduction

theorem variableRealizer_typed (ν : Ty) (A : Formula) (w : Option Var)
    (hw : w.map Var.ty = tau ν A) :
    (Realizer.ofOption (w.map Term.var)
      (by simpa only [Option.isSome_map] using congrArg Option.isSome hw)).Typed := by
  cases w with
  | none =>
      apply (Realizer.typed_cast hw.symm _).mp
      exact True.intro
  | some w =>
      let a := Realizer.ofOption ((some w).map Term.var)
        (by simpa only [Option.isSome_map] using congrArg Option.isSome hw)
      have heq : Realizer.cast hw.symm a = Term.var w := by
        apply Option.some.inj
        exact (Realizer.toOption_cast hw.symm a).trans (Realizer.toOption_ofOption _ _)
      apply (Realizer.typed_cast hw.symm a).mp
      change HasType (Realizer.cast hw.symm a) w.ty
      rw [heq]
      exact .var w

theorem variableRealizer_not_free (ν : Ty) (A : Formula) (w : Option Var)
    (hw : w.map Var.ty = tau ν A) (x : Var) (hx : ∀ v ∈ w, x ≠ v) :
    ∀ t ∈ (Realizer.ofOption (w.map Term.var)
      (by simpa only [Option.isSome_map] using congrArg Option.isSome hw)).toOption,
      x ∉ freeVars t := by
  intro t ht
  rw [Realizer.toOption_ofOption] at ht
  cases w with
  | none => cases ht
  | some w =>
      have ht' : t = .var w := (Option.some.inj (Option.mem_def.mp ht)).symm
      subst t
      simpa [freeVars, freeVarOccurrences] using hx w rfl

@[simp] theorem substBotWithX_bot : substBotWithX .bot = .varX := rfl
@[simp] theorem substBotWithX_varX : substBotWithX .varX = .varX := rfl
@[simp] theorem substBotWithX_atom (t : Term) : substBotWithX (.atom t) = .atom t := rfl
@[simp] theorem substBotWithX_imp (B C : Formula) :
    substBotWithX (.imp B C) = .imp (substBotWithX B) (substBotWithX C) := rfl
@[simp] theorem substBotWithX_all (x : Var) (B : Formula) :
    substBotWithX (.all x B) = .all x (substBotWithX B) := rfl

@[simp]
theorem substBotWithX_impMany (As : List Formula) (B : Formula) :
    substBotWithX (Formula.impMany As B) =
      Formula.impMany (As.map substBotWithX) (substBotWithX B) := by
  induction As with
  | nil => rfl
  | cons A As ih => simp [Formula.impMany, ih]

@[simp]
theorem substBotWithX_allMany (ys : List Var) (A : Formula) :
    substBotWithX (Formula.allMany ys A) = Formula.allMany ys (substBotWithX A) := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [Formula.allMany, ih]

@[simp]
theorem substBotWithX_goalImpliesBot (ys : List Var) (Gs : List Formula) :
    substBotWithX (goalImpliesBot ys Gs) = goalImpliesX ys (Gs.map substBotWithX) := by
  simp [goalImpliesBot, goalImpliesX, Formula.neg]

@[simp]
theorem maxVarIdFormula_substBotWithX (A : Formula) :
    maxVarIdFormula (substBotWithX A) = maxVarIdFormula A := by
  induction A with
  | bot | varX | atom _ => rfl
  | imp B C ihB ihC => simp [maxVarIdFormula, ihB, ihC]
  | all x B ih => simp [maxVarIdFormula, ih]

@[simp]
theorem allVarsFormula_substBotWithX (A : Formula) :
    allVarsFormula (substBotWithX A) = allVarsFormula A := by
  induction A with
  | bot | varX | atom _ => rfl
  | imp B C ihB ihC => simp [allVarsFormula, ihB, ihC]
  | all x B ih => simp [allVarsFormula, ih]

@[simp]
theorem freeVarsFormula_substBotWithX (A : Formula) :
    freeVarsFormula (substBotWithX A) = freeVarsFormula A := by
  induction A with
  | bot | varX | atom _ => rfl
  | imp B C ihB ihC => simp [freeVarsFormula, ihB, ihC]
  | all x B ih => simp [freeVarsFormula, ih]

@[simp]
theorem renameFreeVarFormula_substBotWithX (A : Formula) (x y : Var) :
    renameFreeVarFormula (substBotWithX A) x y =
      substBotWithX (renameFreeVarFormula A x y) := by
  induction A with
  | bot | varX | atom _ => rfl
  | imp B C ihB ihC => simp [renameFreeVarFormula, ihB, ihC]
  | all v B ih =>
      simp only [substBotWithX_all, renameFreeVarFormula]
      split <;> simp [ih]

theorem substFormula_substBotWithX (A : Formula) (x : Var) (t : Term) :
    substFormula (substBotWithX A) x t = substBotWithX (substFormula A x t) := by
  match A with
  | .bot | .varX | .atom _ =>
      simp
  | .imp B C =>
      simp [substFormula_substBotWithX B x t, substFormula_substBotWithX C x t]
  | .all v B =>
      simp only [substBotWithX_all]
      rw [substFormula.eq_def, substFormula.eq_def]
      by_cases hvx : v = x
      · subst hvx; simp
      · have hvxb : (v == x) = false := beq_eq_false_iff_ne.mpr hvx
        simp only [hvxb, Bool.false_eq_true, ↓reduceIte, maxVarIdFormula_substBotWithX]
        split
        · let freshId := Nat.max (maxVarIdFormula B) (Nat.max (maxVarIdTerm t) x.id) + 1
          let v' : Var := ⟨freshId, v.ty⟩
          rw [renameFreeVarFormula_substBotWithX]
          have ih := substFormula_substBotWithX (renameFreeVarFormula B v v') x t
          simpa using ih
        · have ih := substFormula_substBotWithX B x t
          simpa using ih
termination_by formulaSize A
decreasing_by
  all_goals
    simp_wf
    simp [formulaSize, renameFreeVarFormula_size]
    try omega

theorem FormulaWellTyped.substBotWithX {A : Formula} (hA : FormulaWellTyped A) :
    FormulaWellTyped (BBS2002.substBotWithX A) := by
  induction hA with
  | bot => exact .varX
  | varX => exact .varX
  | atom ht => exact .atom ht
  | imp _ _ ih1 ih2 => exact .imp ih1 ih2
  | all x _ ih => exact .all x ih

theorem FormulaBetaREq.substBotWithX {A B : Formula} (h : FormulaBetaREq A B) :
    FormulaBetaREq (BBS2002.substBotWithX A) (BBS2002.substBotWithX B) := by
  induction h with
  | refl C => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | bot => exact .varX
  | varX => exact .varX
  | atom hstep => exact .atom hstep
  | imp _ _ ih1 ih2 => exact .imp ih1 ih2
  | all x _ ih => exact .all x ih
  | all_rename x y C hty hfresh =>
      simp only [substBotWithX_all, ← renameFreeVarFormula_substBotWithX]
      apply FormulaBetaREq.all_rename x y (BBS2002.substBotWithX C) hty
      simpa [allVarsFormula_substBotWithX] using hfresh

theorem mem_freeAssumpVars_substBotProof {M : ProofTerm} {v : AssumpVar}
    (hv : v ∈ freeAssumpVars (substBotProof M)) :
    ∃ u ∈ freeAssumpVars M, v = ⟨u.id, substBotWithX u.formula⟩ := by
  induction M generalizing v with
  | assump u =>
      simp only [substBotProof, freeAssumpVars, List.mem_singleton] at hv ⊢
      exact ⟨u, rfl, hv⟩
  | indNat _ _ | indBool _ _ | axTrue | axFalse _ | efq _ =>
      cases hv
  | lamAssump u M ih =>
      rcases mem_freeAssumpVars_lamAssump.mp hv with ⟨hvM, hne⟩
      rcases ih hvM with ⟨u', hu'M, rfl⟩
      refine ⟨u', ?_, rfl⟩
      exact mem_freeAssumpVars_lamAssump.mpr ⟨hu'M, fun heq => hne (by subst heq; rfl)⟩
  | appAssump M N ihM ihN =>
      rcases mem_freeAssumpVars_appAssump.mp hv with hv | hv
      · rcases ihM hv with ⟨u', hu', rfl⟩
        exact ⟨u', mem_freeAssumpVars_appAssump.mpr (.inl hu'), rfl⟩
      · rcases ihN hv with ⟨u', hu', rfl⟩
        exact ⟨u', mem_freeAssumpVars_appAssump.mpr (.inr hu'), rfl⟩
  | lamTerm x M ih => exact ih hv
  | appTerm M t ih => exact ih hv

theorem SysConfig.allowsFormula.substBotWithX_ZX {sys : SysConfig} {A : Formula}
    (hA : sys.allowsFormula A) :
    SysConfig.ZX.allowsFormula (BBS2002.substBotWithX A) :=
  ⟨FormulaWellTyped.substBotWithX hA.1, .inl rfl⟩

theorem Derivable.substBotProof {M : ProofTerm} {A : Formula}
    (h : Derivable SysConfig.Z0 M A) :
    Derivable SysConfig.ZX (BBS2002.substBotProof M) (substBotWithX A) := by
  induction h with
  | assump u hu =>
      exact .assump ⟨u.id, substBotWithX u.formula⟩ (SysConfig.allowsFormula.substBotWithX_ZX hu)
  | indNat n A hn hA =>
      have h0 := Derivable.indNat (sys := SysConfig.ZX) n (substBotWithX A) hn
        (SysConfig.allowsFormula.substBotWithX_ZX hA)
      simpa [BBS2002.substBotProof, indNatFormula, substFormula_substBotWithX] using h0
  | indBool p A hp hA =>
      have h0 := Derivable.indBool (sys := SysConfig.ZX) p (substBotWithX A) hp
        (SysConfig.allowsFormula.substBotWithX_ZX hA)
      simpa [BBS2002.substBotProof, indBoolFormula, substFormula_substBotWithX] using h0
  | axTrue =>
      exact .axTrue
  | axFalse A hA =>
      exact .axFalse (substBotWithX A) (SysConfig.allowsFormula.substBotWithX_ZX hA)
  | efq A hEfq _ =>
      cases hEfq
  | lamAssump u hu _ ih =>
      exact .lamAssump ⟨u.id, substBotWithX u.formula⟩ (SysConfig.allowsFormula.substBotWithX_ZX hu) ih
  | appAssump _ _ ih1 ih2 =>
      exact .appAssump ih1 ih2
  | lamTerm x hfresh _ ih =>
      refine .lamTerm x ?_ ih
      intro v hv
      rcases mem_freeAssumpVars_substBotProof hv with ⟨u, hu, rfl⟩
      simpa [freeVarsFormula_substBotWithX] using hfresh u hu
  | appTerm t ht _ ih =>
      rw [← substFormula_substBotWithX]
      exact .appTerm t ht ih
  | conv _ hB heq ih =>
      exact .conv ih (SysConfig.allowsFormula.substBotWithX_ZX hB) (FormulaBetaREq.substBotWithX heq)

theorem Provable.substBotProof {A : Formula} (h : Provable SysConfig.Z0 A) :
    Provable SysConfig.ZX (substBotWithX A) := by
  rcases h with ⟨M, hM, hMC⟩
  refine ⟨BBS2002.substBotProof M, Derivable.substBotProof hM, ?_⟩
  apply freeAssumpVars_eq_nil_of_forall_not_mem
  intro v hv
  rcases mem_freeAssumpVars_substBotProof hv with ⟨u, hu, _⟩
  rw [hMC] at hu
  cases hu


/-- Curried type contributed by the computationally relevant assumptions. -/
def implicationType (ν : Ty) : List Formula → Ty → Ty
  | [], ρ => ρ
  | A :: As, ρ =>
      match tau ν A with
      | none => implicationType ν As ρ
      | some σ => .arr σ (implicationType ν As ρ)

theorem tau_impMany (ν : Ty) (As : List Formula) (B : Formula) (ρ : Ty)
    (hB : tau ν B = some ρ) :
    tau ν (Formula.impMany As B) = some (implicationType ν As ρ) := by
  induction As with
  | nil => exact hB
  | cons A As ih =>
      simp only [Formula.impMany, tau, ih, implicationType]
      cases tau ν A <;> rfl

theorem tau_allMany (ν : Ty) (ys : List Var) (B : Formula) (ρ : Ty)
    (hB : tau ν B = some ρ) :
    tau ν (Formula.allMany ys B) = some (Ty.arrMany (ys.map Var.ty) ρ) := by
  induction ys with
  | nil => exact hB
  | cons y ys ih => simp only [Formula.allMany, tau, ih, List.map_cons, Ty.arrMany]

def goalType (ν : Ty) (ys : List Var) (Gs : List Formula) : Ty :=
  Ty.arrMany (ys.map Var.ty) (implicationType ν (Gs.map substBotWithX) ν)

theorem tau_input (ν : Ty) (Ds Gs : List Formula) (ys : List Var) :
    tau ν (substBotWithX (Formula.impMany Ds (goalImpliesBot ys Gs))) =
      some (implicationType ν (Ds.map substBotWithX) (.arr (goalType ν ys Gs) ν)) := by
  simp only [substBotWithX_impMany, substBotWithX_goalImpliesBot, goalImpliesX]
  apply tau_impMany
  simp only [tau, tau_allMany ν ys _ _ (tau_impMany ν (Gs.map substBotWithX) .varX ν rfl)]
  rfl

theorem closed_mr_of_soundness (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    (M : ProofTerm) (B : Formula) (ρ : Ty)
    (hM : Derivable SysConfig.ZX M B) (hClosed : freeAssumpVars M = [])
    (hAdm : AdmissibleForExtraction ν dummy M) (hτ : tau ν B = some ρ) :
    ∃ p : Term, extractRaw ν dummy M = some p ∧ HasType p ρ ∧
      Provable SysConfig.Z (mrFormula ν comp B (Realizer.cast hτ.symm p)) := by
  obtain ⟨r, hr, hTy, N, hN, hFree⟩ := theorem_4_1 ν dummy comp M B hM hAdm
  have hNClosed : freeAssumpVars N = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    obtain ⟨u, hu, _⟩ := hFree v hv
    rw [hClosed] at hu
    cases hu
  let p : Term := Realizer.cast hτ r
  have hp : some p = r.toOption := Realizer.toOption_cast hτ r
  have hCancel : ∀ {τ σ : Option Ty} (h : τ = σ) (q : Realizer τ),
      Realizer.cast h.symm (Realizer.cast h q) = q := by
    intro τ σ h q
    cases h
    rfl
  refine ⟨p, ?_, (Realizer.typed_cast hτ r).mpr hTy, ?_⟩
  · simpa only [extractProgram, hτ] using (hp.trans hr).symm
  · unfold p
    rw [hCancel hτ r]
    exact ⟨N, hN, hNClosed⟩

theorem extracted_input_realizes (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    (Ds Gs : List Formula) (ys : List Var) (M : ProofTerm)
    (hM : Derivable SysConfig.Z0 M (Formula.impMany Ds (goalImpliesBot ys Gs)))
    (hMClosed : freeAssumpVars M = [])
    (hMAdm : AdmissibleForExtraction ν dummy (substBotProof M)) :
    ∃ p : Term, extractRaw ν dummy (substBotProof M) = some p ∧
      HasType p (implicationType ν (Ds.map substBotWithX) (.arr (goalType ν ys Gs) ν)) ∧
      Provable SysConfig.Z
        (mrFormula ν comp (substBotWithX (Formula.impMany Ds (goalImpliesBot ys Gs)))
          (Realizer.cast (tau_input ν Ds Gs ys).symm p)) := by
  apply closed_mr_of_soundness ν dummy comp (substBotProof M) _ _
    (Derivable.substBotProof hM) _ hMAdm (tau_input ν Ds Gs ys)
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro v hv
  obtain ⟨u, hu, _⟩ := mem_freeAssumpVars_substBotProof hv
  rw [hMClosed] at hu
  cases hu

theorem appMany_typed (ys : List Var) (r : Term) (ν : Ty)
    (hr : HasType r (Ty.arrMany (ys.map Var.ty) ν)) :
    HasType (Term.appMany r (ys.map Term.var)) ν := by
  induction ys generalizing r with
  | nil => exact hr
  | cons y ys ih => exact ih (.app r (.var y)) (.app hr (.var y))

theorem lamMany_typed (ys : List Var) {r : Term} {ρ : Ty} (hr : HasType r ρ) :
    HasType (Term.lamMany ys r) (Ty.arrMany (ys.map Var.ty) ρ) := by
  induction ys with
  | nil => exact hr
  | cons y ys ih => exact .lam y ih

def optArrowType : List (Option Var) → Ty → Ty
  | [], ρ => ρ
  | none :: ws, ρ => optArrowType ws ρ
  | some w :: ws, ρ => .arr w.ty (optArrowType ws ρ)

theorem optLamVars_typed (ws : List (Option Var)) {r : Term} {ρ : Ty}
    (hr : HasType r ρ) : HasType (optLamVars ws r) (optArrowType ws ρ) := by
  induction ws with
  | nil => exact hr
  | cons w ws ih => cases w with
    | none => exact ih
    | some w => exact .lam w ih

theorem applyGoalRealizer_typed (ν : Ty) (s : Term) (w : Option Var) (v : Term)
    (hs : HasType s (match w with
      | none => .arr ν ν | some w => .arr w.ty (.arr ν ν)))
    (hv : HasType v ν) : HasType (applyGoalRealizer s w v) ν := by
  cases w with
  | none => exact .app hs hv
  | some w => exact .app (.app hs (.var w)) hv

theorem goalBody_typed (ν : Ty) {n : Nat} (ws : Fin n → Option Var) (ss : Fin n → Term)
    (r : Term) (hr : HasType r ν)
    (hs : ∀ i, HasType (ss i) (match ws i with
      | none => .arr ν ν | some w => .arr w.ty (.arr ν ν))) :
    HasType ((List.zip (List.ofFn ss) (List.ofFn ws)).foldr
      (fun (s, w) acc ↦ applyGoalRealizer s w acc) r) ν := by
  induction n with
  | zero => simpa only [List.ofFn_zero, List.zip_nil_left, List.foldr_nil] using hr
  | succ n ih =>
      simp only [List.ofFn_succ, List.zip_cons_cons, List.foldr_cons]
      apply applyGoalRealizer_typed ν (ss 0) (ws 0) _ (hs 0)
      exact ih (fun i ↦ ws i.succ) (fun i ↦ ss i.succ) (fun i ↦ hs i.succ)

theorem optArrowType_ofFn (ν : Ty) (Gs : List Formula)
    (ws : Fin Gs.length → Option Var)
    (hw : ∀ i, (ws i).map Var.ty = tau ν (substBotWithX (Gs.get i))) :
    optArrowType (List.ofFn ws) ν = implicationType ν (Gs.map substBotWithX) ν := by
  induction Gs with
  | nil => rfl
  | cons G Gs ih =>
      have h0 := hw 0
      simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero] at h0
      simp only [List.ofFn_succ, List.map_cons, implicationType]
      rw [← h0]
      cases hW : ws 0 with
      | none =>
          simp only [Option.map_none, optArrowType]
          exact ih (fun i ↦ ws i.succ) (fun i ↦ hw i.succ)
      | some w =>
          simp only [Option.map_some, optArrowType]
          exact congrArg (Ty.arr w.ty) (ih (fun i ↦ ws i.succ) (fun i ↦ hw i.succ))

theorem goalCombinator_typed (ν : Ty) (ys : List Var) (Gs : List Formula)
    (ws : Fin Gs.length → Option Var) (ss : Fin Gs.length → Term) (r : Term)
    (hw : ∀ i, (ws i).map Var.ty = tau ν (substBotWithX (Gs.get i)))
    (hs : ∀ i, HasType (ss i) (match tau ν (substBotWithX (Gs.get i)) with
      | none => .arr ν ν | some ρ => .arr ρ (.arr ν ν)))
    (hr : HasType r (Ty.arrMany (ys.map Var.ty) ν)) :
    HasType (buildGoalCombinatorTerm ys (List.ofFn ws) (List.ofFn ss) r)
      (goalType ν ys Gs) := by
  unfold buildGoalCombinatorTerm goalType
  rw [← optArrowType_ofFn ν Gs ws hw]
  apply lamMany_typed
  apply optLamVars_typed
  apply goalBody_typed ν ws ss _ (appMany_typed ys r ν hr)
  intro i
  have hsi := hs i
  rw [← hw i] at hsi
  cases hW : ws i <;> simpa only [hW, Option.map_none, Option.map_some] using hsi

theorem applyOptTerms_typed (ν : Ty) (Ds : List Formula)
    (ts : (j : Fin Ds.length) → Realizer (tau ν (substBotWithX (Ds.get j))))
    (hts : ∀ j, (ts j).Typed) (p : Term) (ρ : Ty)
    (hp : HasType p (implicationType ν (Ds.map substBotWithX) ρ)) :
    HasType (applyOptTerms p (List.ofFn fun j ↦ (ts j).toOption)) ρ := by
  induction Ds generalizing p with
  | nil => exact hp
  | cons D Ds ih =>
      have h0 := hts 0
      let tsTail (j : Fin Ds.length) : Realizer (tau ν (substBotWithX (Ds.get j))) := ts j.succ
      have hTail (j : Fin Ds.length) : (tsTail j).Typed := hts j.succ
      simp only [List.ofFn_succ]
      have hτ0 : tau ν (substBotWithX ((D :: Ds).get 0)) = tau ν (substBotWithX D) := rfl
      cases hτ : tau ν (substBotWithX D) with
      | none =>
          have heps : (ts 0).toOption = none :=
            (Realizer.toOption_cast (hτ0.trans hτ) (ts 0)).symm
          rw [heps]
          apply ih tsTail hTail p
          simpa only [List.map_cons, implicationType, hτ] using hp
      | some σ =>
          let t : Term := Realizer.cast (hτ0.trans hτ) (ts 0)
          have hterm : (ts 0).toOption = some t :=
            (Realizer.toOption_cast (hτ0.trans hτ) (ts 0)).symm
          have ht : HasType t σ := (Realizer.typed_cast (hτ0.trans hτ) (ts 0)).mpr h0
          rw [hterm]
          apply ih tsTail hTail (.app p t)
          exact .app (by simpa only [List.map_cons, implicationType, hτ] using hp) ht

/-- Indexed repeated implication elimination, keeping the epsilon convention. -/
def applyImpMany (ν : Ty) (Ds : List Formula) (B : Formula)
    (r : Realizer (tau ν (Formula.impMany (Ds.map substBotWithX) B)))
    (ts : (j : Fin Ds.length) → Realizer (tau ν (substBotWithX (Ds.get j)))) :
    Realizer (tau ν B) :=
  match Ds with
  | [] => r
  | D :: Ds =>
      applyImpMany ν Ds B
        (Realizer.applyImp ν (substBotWithX D) (Formula.impMany (Ds.map substBotWithX) B) r (ts 0))
        (fun j ↦ ts j.succ)

theorem applyImpMany_typed (ν : Ty) (Ds : List Formula) (B : Formula)
    (r : Realizer (tau ν (Formula.impMany (Ds.map substBotWithX) B)))
    (ts : (j : Fin Ds.length) → Realizer (tau ν (substBotWithX (Ds.get j))))
    (hr : r.Typed) (hts : ∀ j, (ts j).Typed) : (applyImpMany ν Ds B r ts).Typed := by
  induction Ds with
  | nil => exact hr
  | cons D Ds ih =>
      exact ih _ (fun j ↦ ts j.succ)
        (Realizer.applyImp_typed ν _ _ r (ts 0) hr (hts 0)) (fun j ↦ hts j.succ)

theorem applyImpMany_toOption (ν : Ty) (Ds : List Formula) (B : Formula)
    (r : Realizer (tau ν (Formula.impMany (Ds.map substBotWithX) B)))
    (ts : (j : Fin Ds.length) → Realizer (tau ν (substBotWithX (Ds.get j))))
    (p : Term) (hp : r.toOption = some p) :
    (applyImpMany ν Ds B r ts).toOption =
      some (applyOptTerms p (List.ofFn fun j ↦ (ts j).toOption)) := by
  induction Ds generalizing p with
  | nil => exact hp
  | cons D Ds ih =>
      change Realizer (tau ν (.imp (substBotWithX D) (Formula.impMany (Ds.map substBotWithX) B))) at r
      let a : Realizer (tau ν (substBotWithX D)) := ts 0
      simp only [applyImpMany, List.ofFn_succ]
      have hApply := Realizer.applyImp_toOption ν (substBotWithX D)
        (Formula.impMany (Ds.map substBotWithX) B) r a
      change (Realizer.toOption
        (τ := tau ν (.imp (substBotWithX D) (Formula.impMany (Ds.map substBotWithX) B))) r) = some p at hp
      rw [hp] at hApply
      change (applyImpMany ν Ds B
        (Realizer.applyImp ν (substBotWithX D) (Formula.impMany (Ds.map substBotWithX) B) r a)
        (fun j ↦ ts j.succ)).toOption =
        some (applyOptTerms p (a.toOption :: List.ofFn (fun j ↦ (ts j.succ).toOption)))
      cases ht0 : a.toOption with
      | none =>
          simp only [ht0] at hApply
          simp only [applyOptTerms]
          exact ih _ (fun j ↦ ts j.succ) p hApply
      | some t =>
          simp only [ht0] at hApply
          simp only [applyOptTerms]
          exact ih _ (fun j ↦ ts j.succ) (.app p t) hApply

theorem impMany_wellTyped (As : List Formula) (B : Formula)
    (hAs : ∀ A ∈ As, FormulaWellTyped A) (hB : FormulaWellTyped B) :
    FormulaWellTyped (Formula.impMany As B) := by
  induction As with
  | nil => exact hB
  | cons A As ih =>
      exact .imp (hAs A (List.mem_cons_self ..))
        (ih (fun C hC ↦ hAs C (List.mem_cons_of_mem A hC)))

/-- Repeated MR implication elimination. The two generic structural MR laws are
explicit parameters here until their independent induction has been completed. -/
theorem applyImpMany_spec (ν : Ty) (comp : CompTerm ν)
    (hc : ∀ A, MRCompatible ν comp A) (hs : ∀ A, MRSubstitution ν comp A)
    (Γ Ds : List Formula) (B : Formula)
    (r : Realizer (tau ν (Formula.impMany (Ds.map substBotWithX) B)))
    (ts : (j : Fin Ds.length) → Realizer (tau ν (substBotWithX (Ds.get j))))
    (hΓ : ∀ A ∈ Γ, SysConfig.Z.allowsFormula A)
    (hDs : ∀ D ∈ Ds, FormulaWellTyped D) (hB : FormulaWellTyped B)
    (hr : r.Typed) (hts : ∀ j, (ts j).Typed)
    (hInput : Provable SysConfig.Z (Formula.impMany Γ
      (mrFormula ν comp (Formula.impMany (Ds.map substBotWithX) B) r)))
    (hArgs : ∀ j, Provable SysConfig.Z (Formula.impMany Γ
      (mrFormula ν comp (substBotWithX (Ds.get j)) (ts j)))) :
    Provable SysConfig.Z (Formula.impMany Γ
      (mrFormula ν comp B (applyImpMany ν Ds B r ts))) := by
  induction Ds with
  | nil => exact hInput
  | cons D Ds ih =>
      change Realizer (tau ν (.imp (substBotWithX D) (Formula.impMany (Ds.map substBotWithX) B))) at r
      let a : Realizer (tau ν (substBotWithX D)) := ts 0
      let rest := Formula.impMany (Ds.map substBotWithX) B
      have hDX : FormulaWellTyped (substBotWithX D) :=
        FormulaWellTyped.substBotWithX (hDs D (List.mem_cons_self ..))
      have hRest : FormulaWellTyped rest := by
        apply impMany_wellTyped _ B _ hB
        intro A hA
        obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hA
        exact FormulaWellTyped.substBotWithX (hDs E (List.mem_cons_of_mem D hE))
      have ha : a.Typed := hts 0
      have hNewTy := Realizer.applyImp_typed ν (substBotWithX D) rest r a hr ha
      have hRAllowed := MrLogic.mr_allowed ν comp (.imp (substBotWithX D) rest) r (.imp hDX hRest) hr
      have hAAllowed := MrLogic.mr_allowed ν comp (substBotWithX D) a hDX ha
      have hNewAllowed := MrLogic.mr_allowed ν comp rest _ hRest hNewTy
      have hMP := MrLogic.mr_imp_elim ν comp hc hs (substBotWithX D) rest r a hDX hRest hr ha
      have hNew := Provable.ctx_mp hΓ hAAllowed hNewAllowed
        (Provable.ctx_mp hΓ hRAllowed (hAAllowed.imp hNewAllowed)
          (Provable.ctx_const hΓ hMP) hInput) (hArgs 0)
      exact ih _ (fun j ↦ ts j.succ)
        (fun E hE ↦ hDs E (List.mem_cons_of_mem D hE)) hNewTy (fun j ↦ hts j.succ)
        hNew (fun j ↦ hArgs j.succ)

/-- The program and its final typing in Theorem 5.1 already follow from soundness;
the realizability calculation establishing the final specification is separate. -/
theorem theorem_5_1_program_and_type
    (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    (Ds Gs : List Formula) (ys : List Var)
    (ts : (j : Fin Ds.length) → Realizer (tau ν (substBotWithX (Ds.get j))))
    (ws : Fin Gs.length → Option Var) (ss : Fin Gs.length → Term)
    (r : Term) (M : ProofTerm)
    (htsTy : ∀ j, (ts j).Typed)
    (hwsTy : ∀ i, (ws i).map Var.ty = tau ν (substBotWithX (Gs.get i)))
    (hssTy : ∀ i, HasType (ss i) (match tau ν (substBotWithX (Gs.get i)) with
      | none => .arr ν ν | some ρ => .arr ρ (.arr ν ν)))
    (hrTy : HasType r (Ty.arrMany (ys.map Var.ty) ν))
    (hM : Derivable SysConfig.Z0 M (Formula.impMany Ds (goalImpliesBot ys Gs)))
    (hMClosed : freeAssumpVars M = [])
    (hMAdm : AdmissibleForExtraction ν dummy (substBotProof M)) :
    ∃ p : Term, extractRaw ν dummy (substBotProof M) = some p ∧
      HasType (.app (applyOptTerms p (List.ofFn fun j ↦ (ts j).toOption))
        (buildGoalCombinatorTerm ys (List.ofFn ws) (List.ofFn ss) r)) ν := by
  obtain ⟨p, hp, hpTy, _⟩ := extracted_input_realizes ν dummy comp Ds Gs ys M hM hMClosed hMAdm
  exact ⟨p, hp, .app (applyOptTerms_typed ν Ds ts htsTy p _ hpTy)
    (goalCombinator_typed ν ys Gs ws ss r hwsTy hssTy hrTy)⟩

def typedGoalStep (ν : Ty) (G R : Formula) (s : Term) (w : Option Var)
    (hs : HasType s (match w with
      | none => .arr ν ν | some w => .arr w.ty (.arr ν ν))) :
    ComputationalLogic.GoalElimStep {t : Term // HasType t ν} :=
  ⟨G, R, fun t ↦ ⟨applyGoalRealizer s w t.val,
    applyGoalRealizer_typed ν s w t.val hs t.property⟩⟩

theorem goalResult_value (ν : Ty) {n : Nat}
    (Gs Rs : Fin n → Formula) (ss : Fin n → Term) (ws : Fin n → Option Var)
    (hs : ∀ i, HasType (ss i) (match ws i with
      | none => .arr ν ν | some w => .arr w.ty (.arr ν ν)))
    (t : {t : Term // HasType t ν}) :
    (ComputationalLogic.goalResult
      (List.ofFn fun i ↦ typedGoalStep ν (Gs i) (Rs i) (ss i) (ws i) (hs i)) t).val =
      (List.zip (List.ofFn ss) (List.ofFn ws)).foldr
        (fun (s, w) acc ↦ applyGoalRealizer s w acc) t.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [ComputationalLogic.goalResult, List.ofFn_succ,
        List.zip_cons_cons, List.foldr_cons, typedGoalStep]
      congr 1
      exact ih (fun i ↦ Gs i.succ) (fun i ↦ Rs i.succ) (fun i ↦ ss i.succ)
        (fun i ↦ ws i.succ) (fun i ↦ hs i.succ)

/-- The propositional composition part of Theorem 5.1, after its displayed goal
eliminators have been instantiated at arbitrary typed candidate terms. -/
theorem goal_body_spec (ν : Ty) (comp : CompTerm ν)
    (Γ Gs : List Formula) (Rs : Fin Gs.length → Formula)
    (ss : Fin Gs.length → Term) (ws : Fin Gs.length → Option Var)
    (hs : ∀ i, HasType (ss i) (match ws i with
      | none => .arr ν ν | some w => .arr w.ty (.arr ν ν)))
    (hΓ : ∀ A ∈ Γ, SysConfig.Z.allowsFormula A)
    (hGs : ∀ A ∈ Gs, SysConfig.Z.allowsFormula A)
    (hRs : ∀ i, SysConfig.Z.allowsFormula (Rs i))
    (t : Term) (ht : HasType t ν)
    (hStep : ∀ i q, HasType q ν → Provable SysConfig.Z
      (Formula.impMany Γ (.imp (Rs i)
        (.imp (.imp (Gs.get i) (comp.apply q))
          (comp.apply (applyGoalRealizer (ss i) (ws i) q))))))
    (hBase : Provable SysConfig.Z (Formula.impMany Γ
      (Formula.impMany Gs (comp.apply t)))) :
    Provable SysConfig.Z (Formula.impMany Γ
      (Formula.impMany (List.ofFn Rs)
        (comp.apply ((List.zip (List.ofFn ss) (List.ofFn ws)).foldr
          (fun (s, w) acc ↦ applyGoalRealizer s w acc) t)))) := by
  let steps := List.ofFn fun i ↦ typedGoalStep ν (Gs.get i) (Rs i) (ss i) (ws i) (hs i)
  have hGoals : steps.map ComputationalLogic.GoalElimStep.goal = Gs := by
    simp only [steps, List.map_ofFn, Function.comp_def, typedGoalStep, List.get_eq_getElem]
    exact List.ofFn_getElem
  have hPremises : steps.map ComputationalLogic.GoalElimStep.premise = List.ofFn Rs := by
    simp only [steps, List.map_ofFn, Function.comp_def, typedGoalStep]
  have hResult := ComputationalLogic.compose_goal_eliminators
    (sys := SysConfig.Z) (fun q : {q : Term // HasType q ν} ↦ comp.apply q.val)
    steps ⟨t, ht⟩ Γ hΓ
    (fun q ↦ ⟨comp.body_wt.substFormula comp.var (comp.var_ty.symm ▸ q.property),
      .inr ((isLFormula_substFormula comp.body comp.var q.val).trans comp.body_isL)⟩)
    (by
      intro step hstep
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hstep
      exact hGs _ (List.get_mem ..))
    (by
      intro step hstep
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hstep
      exact hRs i)
    (by
      intro step hstep q
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hstep
      exact hStep i q.val q.property)
    (by simpa only [hGoals] using hBase)
  rw [hPremises] at hResult
  change Provable SysConfig.Z (Formula.impMany Γ
    (Formula.impMany (List.ofFn Rs)
      (comp.apply (ComputationalLogic.goalResult
        (List.ofFn fun i ↦ typedGoalStep ν (Gs.get i) (Rs i) (ss i) (ws i) (hs i)) ⟨t, ht⟩).val))) at hResult
  rw [goalResult_value] at hResult
  exact hResult

def goalEliminatorType (ν : Ty) : Option Var → Ty
  | none => .arr ν ν
  | some w => .arr w.ty (.arr ν ν)

/-- Instantiate the variable displayed in hypothesis (8), restoring the untouched
context, goal, and realizability premise. Only the two comprehension applications
remain as explicit capture-avoiding substitutions. -/
theorem instantiate_goal_eliminator (ν : Ty) (comp : CompTerm ν)
    (Γ : List Formula) (G : Formula) (s : Term) (w : Option Var) (v : Var)
    (hw : w.map Var.ty = tau ν (substBotWithX G))
    (hv : v.ty = ν)
    (hs : HasType s (goalEliminatorType ν w))
    (hΓ : ∀ D ∈ Γ, SysConfig.Z.allowsFormula D) (hG : SysConfig.Z.allowsFormula G)
    (hΓFresh : ∀ D ∈ Γ, v ∉ freeVarsFormula D)
    (hGFresh : v ∉ freeVarsFormula G) (hWFresh : ∀ x ∈ w, v ≠ x)
    (hCompFresh : v = comp.var ∨ v ∉ freeVarsFormula comp.body)
    (h : Provable SysConfig.Z (Formula.impMany Γ
      (.imp (mrFormula ν comp (substBotWithX G)
          (Realizer.ofOption (w.map Term.var)
            (by simpa only [Option.isSome_map] using congrArg Option.isSome hw)))
        (.imp (.imp G (comp.apply (.var v)))
          (comp.apply (applyGoalRealizer s w (.var v)))))))
    (q : Term) (hq : HasType q ν) :
    Provable SysConfig.Z (Formula.impMany Γ
      (.imp (mrFormula ν comp (substBotWithX G)
          (Realizer.ofOption (w.map Term.var)
            (by simpa only [Option.isSome_map] using congrArg Option.isSome hw)))
        (.imp (.imp G (substFormula (comp.apply (.var v)) v q))
          (substFormula (comp.apply (applyGoalRealizer s w (.var v))) v q)))) := by
  let a := Realizer.ofOption (w.map Term.var)
    (by simpa only [Option.isSome_map] using congrArg Option.isSome hw)
  let R := mrFormula ν comp (substBotWithX G) a
  have hR : SysConfig.Z.allowsFormula R :=
    ⟨mrFormula_wellTyped ν comp (substBotWithX G) a (FormulaWellTyped.substBotWithX hG.1)
      (variableRealizer_typed ν _ w hw), .inr (mrFormula_isL ν comp _ a)⟩
  have hRFresh : v ∉ freeVarsFormula R :=
    mrFormula_not_free ν comp (substBotWithX G) a v
      (by simpa only [freeVarsFormula_substBotWithX] using hGFresh)
      (variableRealizer_not_free ν _ w hw v hWFresh) hCompFresh
  have hComp (t : Term) (ht : HasType t ν) : SysConfig.Z.allowsFormula (comp.apply t) :=
    ⟨comp.body_wt.substFormula comp.var (comp.var_ty.symm ▸ ht),
      .inr ((isLFormula_substFormula comp.body comp.var t).trans comp.body_isL)⟩
  have hVar : HasType (.var v) ν := hv ▸ HasType.var v
  have hC₁ := (hComp (.var v) hVar).substFormula v (hv.symm ▸ hq)
  have hC₂ := (hComp (applyGoalRealizer s w (.var v))
    (applyGoalRealizer_typed ν s w (.var v) (by cases w <;> exact hs) hVar)).substFormula v (hv.symm ▸ hq)
  have hInst := ComputationalLogic.provable_substFormula v q (hv.symm ▸ hq) h
  apply Provable.conv hInst (.impMany hΓ (hR.imp ((hG.imp hC₁).imp hC₂)))
  apply ComputationalLogic.subst_impMany_context_congr Γ _ _ v q hΓFresh
  simp only [substFormula]
  exact .imp
    (substFormula_betaREq_of_not_free R v q (fun hx ↦ hRFresh
      ((ComputationalLogic.mem_formula_occurrences_iff R v).mp hx)))
    (.imp (.imp
      (substFormula_betaREq_of_not_free G v q (fun hx ↦ hGFresh
        ((ComputationalLogic.mem_formula_occurrences_iff G v).mp hx)))
      (.refl _)) (.refl _))

theorem subst_applyGoalRealizer (s : Term) (w : Option Var) (v : Var) (q : Term)
    (hs : v ∉ freeVars s) (hw : ∀ x ∈ w, v ≠ x) :
    BetaREq (substTerm (applyGoalRealizer s w (.var v)) v q)
      (applyGoalRealizer s w q) := by
  have hs' : v ∉ freeVarOccurrences s := by
    simpa only [freeVars, List.mem_eraseDups] using hs
  have hS := BetaREq.of_alpha (substTerm_alphaEq_of_not_free s v q hs')
  cases w with
  | none =>
      simp only [applyGoalRealizer, substTerm, beq_self_eq_true, ↓reduceIte]
      exact .app hS (.refl q)
  | some w =>
      have hwv : w ≠ v := Ne.symm (hw w rfl)
      simp only [applyGoalRealizer, substTerm, beq_self_eq_true, ↓reduceIte,
        beq_eq_false_iff_ne.mpr hwv, Bool.false_eq_true]
      exact .app (.app hS (.refl (.var w))) (.refl q)

/-- Hypothesis (8) is uniform in its displayed candidate variable. The source
freshness conditions justify specialization at every term of the witness type. -/
theorem goal_eliminator_spec (ν : Ty) (comp : CompTerm ν)
    (Γ : List Formula) (G : Formula) (s : Term) (w : Option Var) (v : Var)
    (hw : w.map Var.ty = tau ν (substBotWithX G))
    (hv : v.ty = ν)
    (hs : HasType s (goalEliminatorType ν w))
    (hΓ : ∀ D ∈ Γ, SysConfig.Z.allowsFormula D) (hG : SysConfig.Z.allowsFormula G)
    (hΓFresh : ∀ D ∈ Γ, v ∉ freeVarsFormula D)
    (hGFresh : v ∉ freeVarsFormula G) (hWFresh : ∀ x ∈ w, v ≠ x)
    (hSFresh : v ∉ freeVars s)
    (hCompFresh : v = comp.var ∨ v ∉ freeVarsFormula comp.body)
    (h : Provable SysConfig.Z (Formula.impMany Γ
      (.imp (mrFormula ν comp (substBotWithX G)
          (Realizer.ofOption (w.map Term.var)
            (by simpa only [Option.isSome_map] using congrArg Option.isSome hw)))
        (.imp (.imp G (comp.apply (.var v)))
          (comp.apply (applyGoalRealizer s w (.var v)))))))
    (q : Term) (hq : HasType q ν) :
    Provable SysConfig.Z (Formula.impMany Γ
      (.imp (mrFormula ν comp (substBotWithX G)
          (Realizer.ofOption (w.map Term.var)
            (by simpa only [Option.isSome_map] using congrArg Option.isSome hw)))
        (.imp (.imp G (comp.apply q))
          (comp.apply (applyGoalRealizer s w q))))) := by
  have hInst := instantiate_goal_eliminator ν comp Γ G s w v hw hv hs hΓ hG
    hΓFresh hGFresh hWFresh hCompFresh h q hq
  have hC₁ : FormulaBetaREq (substFormula (comp.apply (.var v)) v q) (comp.apply q) := by
    have hEq := FormulaConversion.subst_formula_comprehension comp.body comp.var v
      (.var v) q hCompFresh
    simpa only [CompTerm.apply, substTerm, beq_self_eq_true, ↓reduceIte] using hEq
  have hC₂ : FormulaBetaREq
      (substFormula (comp.apply (applyGoalRealizer s w (.var v))) v q)
      (comp.apply (applyGoalRealizer s w q)) :=
    .trans (FormulaConversion.subst_formula_comprehension comp.body comp.var v
      (applyGoalRealizer s w (.var v)) q hCompFresh)
      (FormulaConversion.subst_formula_congr comp.var (.refl comp.body)
        (subst_applyGoalRealizer s w v q hSFresh hWFresh))
  let a := Realizer.ofOption (w.map Term.var)
    (by simpa only [Option.isSome_map] using congrArg Option.isSome hw)
  have hR : SysConfig.Z.allowsFormula (mrFormula ν comp (substBotWithX G) a) :=
    ⟨mrFormula_wellTyped ν comp (substBotWithX G) a (FormulaWellTyped.substBotWithX hG.1)
      (variableRealizer_typed ν _ w hw), .inr (mrFormula_isL ν comp _ a)⟩
  have hComp (t : Term) (ht : HasType t ν) : SysConfig.Z.allowsFormula (comp.apply t) :=
    ⟨comp.body_wt.substFormula comp.var (comp.var_ty.symm ▸ ht),
      .inr ((isLFormula_substFormula comp.body comp.var t).trans comp.body_isL)⟩
  exact ComputationalLogic.ctx_conv hΓ
    (hR.imp ((hG.imp (hComp q hq)).imp (hComp (applyGoalRealizer s w q)
      (applyGoalRealizer_typed ν s w q (by cases w <;> exact hs) hq))))
    (.imp (.refl _) (.imp (.imp (.refl G) hC₁) hC₂)) hInst

def goalPremise (ν : Ty) (comp : CompTerm ν) (G : Formula) (w : Option Var)
    (hw : w.map Var.ty = tau ν (substBotWithX G)) : Formula :=
  mrFormula ν comp (substBotWithX G)
    (Realizer.ofOption (w.map Term.var)
      (by simpa only [Option.isSome_map] using congrArg Option.isSome hw))

/-- The full unquantified goal matrix, using precisely hypotheses (8) and (9)
and the parts of the source freshness convention needed for their composition. -/
theorem goal_matrix_spec (ν : Ty) (comp : CompTerm ν)
    (Ds Gs : List Formula) (ys : List Var)
    (ws : Fin Gs.length → Option Var) (ss : Fin Gs.length → Term)
    (vs : Fin Gs.length → Var) (r : Term)
    (hDs : ∀ D ∈ Ds, SysConfig.Z.allowsFormula D)
    (hGs : ∀ G ∈ Gs, SysConfig.Z.allowsFormula G)
    (hwsTy : ∀ i, (ws i).map Var.ty = tau ν (substBotWithX (Gs.get i)))
    (hvsTy : ∀ i, (vs i).ty = ν)
    (hssTy : ∀ i, HasType (ss i) (match tau ν (substBotWithX (Gs.get i)) with
      | none => .arr ν ν | some ρ => .arr ρ (.arr ν ν)))
    (hrTy : HasType r (Ty.arrMany (ys.map Var.ty) ν))
    (hvDs : ∀ i, ∀ D ∈ Ds, vs i ∉ freeVarsFormula D)
    (hvGs : ∀ i, vs i ∉ freeVarsFormula (Gs.get i))
    (hvWs : ∀ i, ∀ w ∈ ws i, vs i ≠ w)
    (hvSs : ∀ i, vs i ∉ freeVars (ss i))
    (hvComp : ∀ i, vs i = comp.var ∨ vs i ∉ freeVarsFormula comp.body)
    (h8 : ∀ i, Provable SysConfig.Z (Formula.impMany Ds
      (.imp (goalPremise ν comp (Gs.get i) (ws i) (hwsTy i))
        (.imp (.imp (Gs.get i) (comp.apply (.var (vs i))))
          (comp.apply (applyGoalRealizer (ss i) (ws i) (.var (vs i))))))))
    (h9 : Provable SysConfig.Z (Formula.impMany Ds (Formula.allMany ys
      (Formula.impMany Gs (comp.apply (Term.appMany r (ys.map Term.var))))))) :
    Provable SysConfig.Z (Formula.impMany Ds
      (Formula.impMany (List.ofFn fun i ↦ goalPremise ν comp (Gs.get i) (ws i) (hwsTy i))
        (comp.apply ((List.zip (List.ofFn ss) (List.ofFn ws)).foldr
          (fun (s, w) acc ↦ applyGoalRealizer s w acc)
          (Term.appMany r (ys.map Term.var)))))) := by
  have hComponents (i : Fin Gs.length) : HasType (ss i) (match ws i with
      | none => .arr ν ν | some w => .arr w.ty (.arr ν ν)) := by
    have hsi := hssTy i
    rw [← hwsTy i] at hsi
    cases hW : ws i <;> simpa only [hW, Option.map_none, Option.map_some] using hsi
  have hBaseTy := appMany_typed ys r ν hrTy
  have hBaseAllowed : SysConfig.Z.allowsFormula (comp.apply (Term.appMany r (ys.map Term.var))) :=
    ⟨comp.body_wt.substFormula comp.var (comp.var_ty.symm ▸ hBaseTy),
      .inr ((isLFormula_substFormula comp.body comp.var _).trans comp.body_isL)⟩
  apply goal_body_spec ν comp Ds Gs _ ss ws hComponents hDs hGs
    (fun i ↦ ⟨mrFormula_wellTyped ν comp _ _
      (FormulaWellTyped.substBotWithX (hGs _ (List.get_mem ..)).1)
      (variableRealizer_typed ν _ (ws i) (hwsTy i)),
      .inr (mrFormula_isL ν comp _ _)⟩)
    _ hBaseTy
  · intro i q hq
    exact goal_eliminator_spec ν comp Ds (Gs.get i) (ss i) (ws i) (vs i)
      (hwsTy i) (hvsTy i) (hComponents i)
      hDs (hGs _ (List.get_mem ..))
      (hvDs i) (hvGs i) (hvWs i) (hvSs i) (hvComp i) (h8 i) q hq
  · exact ComputationalLogic.ctx_allMany_elim_self Ds ys _ hDs (.impMany hGs hBaseAllowed) h9

theorem option_binders_distinct_of_lt {n : Nat} (ws : Fin n → Option Var)
    (hNodup : ((List.ofFn ws).filterMap id).Nodup)
    (i j : Fin n) (hji : j.val < i.val) (w : Var) (hw : w ∈ ws i)
    (z : Var) (hz : z ∈ ws j) : w ≠ z := by
  have hp := List.pairwise_filterMap.mp hNodup
  have hij := List.pairwise_iff_getElem.mp hp j.val i.val
    (by simpa only [List.length_ofFn] using j.isLt)
    (by simpa only [List.length_ofFn] using i.isLt) hji
  simp only [List.getElem_ofFn] at hij
  exact Ne.symm (hij z (Option.mem_def.mp hz) w (Option.mem_def.mp hw))

/-- Add the alternating realizer quantifiers and the outer object quantifiers to
the established matrix. All eigenvariable conditions follow from the displayed
source freshness convention and the proved MR support bound. -/
theorem quantify_goal_spec (ν : Ty) (comp : CompTerm ν)
    (Ds Gs : List Formula) (ys : List Var)
    (ws : Fin Gs.length → Option Var)
    (hw : ∀ i, (ws i).map Var.ty = tau ν (substBotWithX (Gs.get i)))
    (C : Formula) (hC : SysConfig.Z.allowsFormula C)
    (hDs : ∀ D ∈ Ds, SysConfig.Z.allowsFormula D)
    (hGs : ∀ G ∈ Gs, SysConfig.Z.allowsFormula G)
    (hNodup : ((List.ofFn ws).filterMap id).Nodup)
    (hyDs : ∀ y ∈ ys, ∀ D ∈ Ds, y ∉ freeVarsFormula D)
    (hwDs : ∀ w ∈ (List.ofFn ws).filterMap id, ∀ D ∈ Ds, w ∉ freeVarsFormula D)
    (hwGs : ∀ w ∈ (List.ofFn ws).filterMap id, ∀ G ∈ Gs, w ∉ freeVarsFormula G)
    (hwComp : ∀ w ∈ (List.ofFn ws).filterMap id,
      w = comp.var ∨ w ∉ freeVarsFormula comp.body)
    (h : Provable SysConfig.Z (Formula.impMany Ds
      (Formula.impMany (List.ofFn fun i ↦ goalPremise ν comp (Gs.get i) (ws i) (hw i)) C))) :
    Provable SysConfig.Z (Formula.impMany Ds (Formula.allMany ys
      (ComputationalLogic.quantifiedMatrix
        (List.ofFn fun i ↦ (ws i, goalPremise ν comp (Gs.get i) (ws i) (hw i))) C))) := by
  let Rs (i : Fin Gs.length) := goalPremise ν comp (Gs.get i) (ws i) (hw i)
  have hRs (i : Fin Gs.length) : SysConfig.Z.allowsFormula (Rs i) :=
    ⟨mrFormula_wellTyped ν comp _ _
      (FormulaWellTyped.substBotWithX (hGs _ (List.get_mem ..)).1)
      (variableRealizer_typed ν _ (ws i) (hw i)),
      .inr (mrFormula_isL ν comp _ _)⟩
  have hwMem (i : Fin Gs.length) (w : Var) (hwi : w ∈ ws i) :
      w ∈ (List.ofFn ws).filterMap id :=
    List.mem_filterMap.mpr ⟨ws i, List.mem_ofFn.mpr ⟨i, rfl⟩, Option.mem_def.mp hwi⟩
  have hMatrix : Provable SysConfig.Z (Formula.impMany Ds
      (ComputationalLogic.quantifiedMatrix (List.ofFn fun i ↦ (ws i, Rs i)) C)) := by
    apply ComputationalLogic.quantify_matrix Ds ws Rs C hDs hRs hC
      (fun i w hwi D hD ↦ hwDs w (hwMem i w hwi) D hD) _ h
    intro i j hji w hwi
    apply mrFormula_not_free ν comp (substBotWithX (Gs.get j)) _ w
    · simpa only [freeVarsFormula_substBotWithX] using hwGs w (hwMem i w hwi) _ (List.get_mem ..)
    · exact variableRealizer_not_free ν _ (ws j) (hw j) w
        (option_binders_distinct_of_lt ws hNodup i j hji w hwi)
    · exact hwComp w (hwMem i w hwi)
  apply ComputationalLogic.ctx_allMany_intro Ds ys _ hDs _ hyDs hMatrix
  apply ComputationalLogic.quantifiedMatrix_allowed _ C hC
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact hRs i

/-- The quantified goal matrix derived directly from the exact freshness and
logical hypotheses of the replacement Theorem 5.1. -/
theorem source_goal_matrix (ν : Ty) (comp : CompTerm ν)
    (Ds Gs : List Formula) (ys : List Var)
    (ws : Fin Gs.length → Option Var) (ss : Fin Gs.length → Term)
    (vs : Fin Gs.length → Var) (r : Term)
    (hDs : ∀ D ∈ Ds, FormulaWellTyped D ∧ isLFormula D = true)
    (hGs : ∀ G ∈ Gs, FormulaWellTyped G ∧ isLFormula G = true)
    (hwsTy : ∀ i, (ws i).map Var.ty = tau ν (substBotWithX (Gs.get i)))
    (hvsTy : ∀ i, (vs i).ty = ν)
    (hssTy : ∀ i, HasType (ss i) (match tau ν (substBotWithX (Gs.get i)) with
      | none => .arr ν ν | some ρ => .arr ρ (.arr ν ν)))
    (hrTy : HasType r (Ty.arrMany (ys.map Var.ty) ν))
    (hBindersFresh :
      let wVars := (List.ofFn ws).filterMap id
      let vVars := List.ofFn vs
      (ys ++ wVars ++ vVars).Nodup ∧
      (∀ y ∈ ys, ∀ D ∈ Ds, y ∉ freeVarsFormula D) ∧
      (∀ z ∈ wVars ++ vVars, ∀ i, z ∉ freeVars (ss i)) ∧
      (∀ z ∈ ys ++ wVars, z ∉ freeVars r) ∧
      (∀ z ∈ wVars ++ vVars, ∀ D ∈ Ds, z ∉ freeVarsFormula D) ∧
      (∀ z ∈ wVars ++ vVars, ∀ G ∈ Gs, z ∉ freeVarsFormula G) ∧
      (∀ z ∈ ys ++ wVars ++ vVars,
        z = comp.var ∨ z ∉ freeVarsFormula comp.body))
    (h8 : ∀ i, Provable SysConfig.Z (Formula.impMany Ds
      (.imp (goalPremise ν comp (Gs.get i) (ws i) (hwsTy i))
        (.imp (.imp (Gs.get i) (comp.apply (.var (vs i))))
          (comp.apply (applyGoalRealizer (ss i) (ws i) (.var (vs i))))))))
    (h9 : Provable SysConfig.Z (Formula.impMany Ds (Formula.allMany ys
      (Formula.impMany Gs (comp.apply (Term.appMany r (ys.map Term.var))))))) :
    Provable SysConfig.Z (Formula.impMany Ds (Formula.allMany ys
      (ComputationalLogic.quantifiedMatrix
        (List.ofFn fun i ↦ (ws i, goalPremise ν comp (Gs.get i) (ws i) (hwsTy i)))
        (comp.apply ((List.zip (List.ofFn ss) (List.ofFn ws)).foldr
          (fun (s, w) acc ↦ applyGoalRealizer s w acc)
          (Term.appMany r (ys.map Term.var))))))) := by
  let wVars := (List.ofFn ws).filterMap id
  let vVars := List.ofFn vs
  rcases hBindersFresh with ⟨hNodup, hyDs, hSsFresh, _, hDsFresh, hGsFresh, hCompFresh⟩
  have hDsAllowed : ∀ D ∈ Ds, SysConfig.Z.allowsFormula D :=
    fun D hD ↦ ⟨(hDs D hD).1, .inr (hDs D hD).2⟩
  have hGsAllowed : ∀ G ∈ Gs, SysConfig.Z.allowsFormula G :=
    fun G hG ↦ ⟨(hGs G hG).1, .inr (hGs G hG).2⟩
  have hND : ((ys ++ wVars) ++ vVars).Nodup := by
    simpa only [List.append_assoc] using hNodup
  have hParts := List.nodup_append.mp hND
  have hWNodup : wVars.Nodup := (List.nodup_append.mp hParts.1).2.1
  have hwMem (i : Fin Gs.length) (w : Var) (hwi : w ∈ ws i) : w ∈ wVars :=
    List.mem_filterMap.mpr ⟨ws i, List.mem_ofFn.mpr ⟨i, rfl⟩, Option.mem_def.mp hwi⟩
  have hvMem (i : Fin Gs.length) : vs i ∈ vVars := List.mem_ofFn.mpr ⟨i, rfl⟩
  have hwFull (w : Var) (hw : w ∈ wVars) : w ∈ ys ++ wVars ++ vVars := by
    have h : w ∈ (ys ++ wVars) ++ vVars :=
      List.mem_append_left _ (List.mem_append_right _ hw)
    simpa only [List.append_assoc] using h
  have hvFull (i : Fin Gs.length) : vs i ∈ ys ++ wVars ++ vVars := by
    have h : vs i ∈ (ys ++ wVars) ++ vVars := List.mem_append_right _ (hvMem i)
    simpa only [List.append_assoc] using h
  have hComponents (i : Fin Gs.length) : HasType (ss i) (match ws i with
      | none => .arr ν ν | some w => .arr w.ty (.arr ν ν)) := by
    have hsi := hssTy i
    rw [← hwsTy i] at hsi
    cases hW : ws i <;> simpa only [hW, Option.map_none, Option.map_some] using hsi
  have hBodyTy := goalBody_typed ν ws ss (Term.appMany r (ys.map Term.var))
    (appMany_typed ys r ν hrTy) hComponents
  apply quantify_goal_spec ν comp Ds Gs ys ws hwsTy _
    ⟨comp.body_wt.substFormula comp.var (comp.var_ty.symm ▸ hBodyTy),
      .inr ((isLFormula_substFormula comp.body comp.var _).trans comp.body_isL)⟩
    hDsAllowed hGsAllowed hWNodup hyDs
    (fun w hw D hD ↦ hDsFresh w (List.mem_append_left _ hw) D hD)
    (fun w hw G hG ↦ hGsFresh w (List.mem_append_left _ hw) G hG)
    (fun w hw ↦ hCompFresh w (hwFull w hw))
  exact goal_matrix_spec ν comp Ds Gs ys ws ss vs r hDsAllowed hGsAllowed hwsTy hvsTy hssTy hrTy
    (fun i D hD ↦ hDsFresh _ (List.mem_append_right _ (hvMem i)) D hD)
    (fun i ↦ hGsFresh _ (List.mem_append_right _ (hvMem i)) _ (List.get_mem ..))
    (fun i w hw ↦ Ne.symm (hParts.2.2 w (List.mem_append_right _ (hwMem i w hw)) _ (hvMem i)))
    (fun i ↦ hSsFresh _ (List.mem_append_right _ (hvMem i)) i)
    (fun i ↦ hCompFresh _ (hvFull i)) h8 h9

end BBS2002.V2.ComputationalReduction


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


/- Local checked proof module: Abstraction51 -/

namespace BBS2002.V2.ComputationalAbstraction

open ComputationalReduction

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

theorem not_free_impMany (As : List Formula) (B : Formula) (x : Var)
    (hAs : ∀ A ∈ As, x ∉ freeVarsFormula A) (hB : x ∉ freeVarsFormula B) :
    x ∉ freeVarsFormula (Formula.impMany As B) := by
  induction As with
  | nil => exact hB
  | cons A As ih =>
      simp only [Formula.impMany, freeVarsFormula, List.mem_eraseDups, List.mem_append, not_or]
      exact ⟨hAs A (List.mem_cons_self ..), ih (fun C hC ↦ hAs C (List.mem_cons_of_mem A hC))⟩

theorem mr_impMany_optLam (ν : Ty) (comp : CompTerm ν)
    (hc : ∀ A, MRCompatible ν comp A) (hs : ∀ A, MRSubstitution ν comp A)
    (Gs : List Formula) (ws : Fin Gs.length → Option Var)
    (hw : ∀ i, (ws i).map Var.ty = tau ν (substBotWithX (Gs.get i)))
    (t : Term) (r : Realizer (tau ν (Formula.impMany (Gs.map substBotWithX) .varX)))
    (hr : r.toOption = some (optLamVars (List.ofFn ws) t))
    (hwGs : ∀ w ∈ (List.ofFn ws).filterMap id, ∀ G ∈ Gs, w ∉ freeVarsFormula G)
    (hwC : ∀ w ∈ (List.ofFn ws).filterMap id,
      w = comp.var ∨ w ∉ freeVarsFormula comp.body) :
    FormulaBetaREq (mrFormula ν comp (Formula.impMany (Gs.map substBotWithX) .varX) r)
      (ComputationalLogic.quantifiedMatrix
        (List.ofFn fun i ↦ (ws i, goalPremise ν comp (Gs.get i) (ws i) (hw i))) (comp.apply t)) := by
  induction Gs with
  | nil =>
      have hr' : r = t := Option.some.inj hr
      subst r
      change FormulaBetaREq (mrFormula ν comp .varX t) (comp.apply t)
      rw [mrFormula.eq_def ν comp .varX t]
      exact .refl _
  | cons G Gs ih =>
      let wsTail (i : Fin Gs.length) := ws i.succ
      have hwTail (i : Fin Gs.length) : (wsTail i).map Var.ty = tau ν (substBotWithX (Gs.get i)) := hw i.succ
      let rest := Formula.impMany (Gs.map substBotWithX) .varX
      let σ := implicationType ν (Gs.map substBotWithX) ν
      have hRest : tau ν rest = some σ := tau_impMany ν _ .varX ν rfl
      let tailTerm := optLamVars (List.ofFn wsTail) t
      let tailR : Realizer (tau ν rest) := Realizer.cast hRest.symm tailTerm
      have hTailMem (w : Var) (hw : w ∈ (List.ofFn wsTail).filterMap id) :
          w ∈ (List.ofFn ws).filterMap id := by
        obtain ⟨o, ho, how⟩ := List.mem_filterMap.mp hw
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ho
        exact List.mem_filterMap.mpr ⟨ws i.succ, List.mem_ofFn.mpr ⟨i.succ, rfl⟩, how⟩
      have hTail := ih wsTail hwTail tailR (Realizer.toOption_cast hRest.symm tailTerm)
        (fun w hw E hE ↦ hwGs w (hTailMem w hw) E (List.mem_cons_of_mem G hE))
        (fun w hw ↦ hwC w (hTailMem w hw))
      change Realizer (tau ν (.imp (substBotWithX G) rest)) at r
      change (Realizer.toOption (τ := tau ν (.imp (substBotWithX G) rest)) r) =
        some (optLamVars (List.ofFn ws) t) at hr
      change FormulaBetaREq (mrFormula ν comp (.imp (substBotWithX G) rest) r) _
      have h0 := hw 0
      change (ws 0).map Var.ty = tau ν (substBotWithX G) at h0
      let a0 : Realizer (tau ν (substBotWithX G)) := Realizer.ofOption ((ws 0).map Term.var)
        (by simpa only [Option.isSome_map] using congrArg Option.isSome h0)
      have ha0 : a0.toOption = (ws 0).map Term.var := Realizer.toOption_ofOption _ _
      rw [List.ofFn_succ] at hr ⊢
      change FormulaBetaREq (mrFormula ν comp (.imp (substBotWithX G) rest) r)
        (ComputationalLogic.quantifiedMatrix
          ((ws 0, mrFormula ν comp (substBotWithX G) a0) ::
            List.ofFn (fun i ↦ (wsTail i, goalPremise ν comp (Gs.get i) (wsTail i) (hwTail i))))
          (comp.apply t))
      cases hw0 : ws 0 with
      | none =>
          have hA : tau ν (substBotWithX G) = none := by simpa only [hw0, Option.map_none] using h0.symm
          have hr' : r.toOption = some tailTerm := by simpa only [hw0, optLamVars, tailTerm, wsTail] using hr
          refine (mr_imp_epsilon ν comp hc _ rest σ hA hRest tailTerm r hr').trans ?_
          apply FormulaBetaREq.imp _ hTail
          apply hc (substBotWithX G) (substBotWithX G) (.refl _)
          have hl : (Realizer.cast hA.symm ()).toOption = none := Realizer.toOption_cast hA.symm ()
          change Option.Rel BetaREq (Realizer.cast hA.symm ()).toOption a0.toOption
          rw [hl, ha0, hw0]
          exact .none
      | some w =>
          have hA : tau ν (substBotWithX G) = some w.ty := by simpa only [hw0, Option.map_some] using h0.symm
          have hr' : r.toOption = some (.lam w tailTerm) := by simpa only [hw0, optLamVars, tailTerm, wsTail] using hr
          have hwMem : w ∈ (List.ofFn ws).filterMap id :=
            List.mem_filterMap.mpr ⟨ws 0, List.mem_ofFn.mpr ⟨0, rfl⟩, hw0⟩
          have hwG : w ∉ freeVarsFormula (substBotWithX G) := by
            simpa only [freeVarsFormula_substBotWithX] using hwGs w hwMem G (List.mem_cons_self ..)
          have hwRest : w ∉ freeVarsFormula rest := by
            apply not_free_impMany _ .varX w _ (by simp [freeVarsFormula])
            intro A hA
            obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hA
            simpa only [freeVarsFormula_substBotWithX] using hwGs w hwMem E (List.mem_cons_of_mem G hE)
          refine (mr_imp_lambda ν comp hc hs _ rest w.ty σ hA hRest w rfl tailTerm r hr'
            hwG hwRest (hwC w hwMem)).trans (.all w (.imp ?_ hTail))
          apply hc (substBotWithX G) (substBotWithX G) (.refl _)
          have hl : (Realizer.cast hA.symm (.var w)).toOption = some (.var w) :=
            Realizer.toOption_cast hA.symm (.var w)
          change Option.Rel BetaREq (Realizer.cast hA.symm (.var w)).toOption a0.toOption
          rw [hl, ha0, hw0]
          exact .some (.refl _)

theorem allMany_congr (xs : List Var) {A B : Formula} (h : FormulaBetaREq A B) :
    FormulaBetaREq (Formula.allMany xs A) (Formula.allMany xs B) := by
  induction xs with
  | nil => exact h
  | cons x xs ih => exact .all x ih

theorem mr_allMany_lam (ν : Ty) (comp : CompTerm ν)
    (hc : ∀ A, MRCompatible ν comp A) (hs : ∀ A, MRSubstitution ν comp A)
    (xs : List Var) (B : Formula) (ρ : Ty) (hB : tau ν B = some ρ) (t : Term)
    (r : Realizer (tau ν (Formula.allMany xs B)))
    (hr : r.toOption = some (Term.lamMany xs t))
    (hxC : ∀ x ∈ xs, x = comp.var ∨ x ∉ freeVarsFormula comp.body) :
    FormulaBetaREq (mrFormula ν comp (Formula.allMany xs B) r)
      (Formula.allMany xs (mrFormula ν comp B (Realizer.cast hB.symm t))) := by
  induction xs with
  | nil =>
      change Realizer (tau ν B) at r
      change r.toOption = some t at hr
      apply hc B B (.refl B)
      have hout : (Realizer.cast hB.symm t).toOption = some t := Realizer.toOption_cast hB.symm t
      rw [hr, hout]
      exact .some (.refl _)
  | cons x xs ih =>
      have hRest := tau_allMany ν xs B ρ hB
      have hOne := mr_all_lambda ν comp hc hs x (Formula.allMany xs B) _ hRest
        (Term.lamMany xs t) r hr (hxC x (List.mem_cons_self ..))
      exact hOne.trans (.all x (ih _ (Realizer.toOption_cast hRest.symm (Term.lamMany xs t))
        (fun y hy ↦ hxC y (List.mem_cons_of_mem x hy))))

theorem mr_goalCombinator (ν : Ty) (comp : CompTerm ν)
    (hc : ∀ A, MRCompatible ν comp A) (hs : ∀ A, MRSubstitution ν comp A)
    (ys : List Var) (Gs : List Formula) (ws : Fin Gs.length → Option Var)
    (ss : Fin Gs.length → Term) (r : Term)
    (hw : ∀ i, (ws i).map Var.ty = tau ν (substBotWithX (Gs.get i)))
    (q : Realizer (tau ν (Formula.allMany ys (Formula.impMany (Gs.map substBotWithX) .varX))))
    (hq : q.toOption = some (buildGoalCombinatorTerm ys (List.ofFn ws) (List.ofFn ss) r))
    (hwGs : ∀ w ∈ (List.ofFn ws).filterMap id, ∀ G ∈ Gs, w ∉ freeVarsFormula G)
    (hwC : ∀ w ∈ (List.ofFn ws).filterMap id,
      w = comp.var ∨ w ∉ freeVarsFormula comp.body)
    (hyC : ∀ y ∈ ys, y = comp.var ∨ y ∉ freeVarsFormula comp.body) :
    FormulaBetaREq
      (mrFormula ν comp (Formula.allMany ys (Formula.impMany (Gs.map substBotWithX) .varX)) q)
      (Formula.allMany ys (ComputationalLogic.quantifiedMatrix
        (List.ofFn fun i ↦ (ws i, goalPremise ν comp (Gs.get i) (ws i) (hw i)))
        (comp.apply ((List.zip (List.ofFn ss) (List.ofFn ws)).foldr
          (fun (s, w) acc ↦ applyGoalRealizer s w acc)
          (Term.appMany r (ys.map Term.var)))))) := by
  let body := (List.zip (List.ofFn ss) (List.ofFn ws)).foldr
    (fun (s, w) acc ↦ applyGoalRealizer s w acc) (Term.appMany r (ys.map Term.var))
  have hτ := tau_impMany ν (Gs.map substBotWithX) .varX ν rfl
  have hAll := mr_allMany_lam ν comp hc hs ys (Formula.impMany (Gs.map substBotWithX) .varX)
    _ hτ (optLamVars (List.ofFn ws) body) q hq hyC
  exact hAll.trans (allMany_congr ys (mr_impMany_optLam ν comp hc hs Gs ws hw body
    (Realizer.cast hτ.symm (optLamVars (List.ofFn ws) body))
    (Realizer.toOption_cast hτ.symm (optLamVars (List.ofFn ws) body)) hwGs hwC))

end BBS2002.V2.ComputationalAbstraction


/- Local checked proof module: Final51 -/

namespace BBS2002.V2

open ComputationalReduction ComputationalAbstraction

theorem theorem_5_1_of_mr_laws
    (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    (hc : ∀ A, MRCompatible ν comp A) (hs : ∀ A, MRSubstitution ν comp A)
    (Ds Gs : List Formula) (ys : List Var)
    (ts : (j : Fin Ds.length) → Realizer (tau ν (substBotWithX (Ds.get j))))
    (ws : Fin Gs.length → Option Var) (ss : Fin Gs.length → Term)
    (vs : Fin Gs.length → Var) (r : Term) (M : ProofTerm)
    (hDs : ∀ D ∈ Ds, FormulaWellTyped D ∧ isLFormula D = true)
    (hGs : ∀ G ∈ Gs, FormulaWellTyped G ∧ isLFormula G = true)
    (htsTy : ∀ j, (ts j).Typed)
    (hwsTy : ∀ i, (ws i).map Var.ty = tau ν (substBotWithX (Gs.get i)))
    (hvsTy : ∀ i, (vs i).ty = ν)
    (hssTy : ∀ i,
      HasType (ss i)
        (match tau ν (substBotWithX (Gs.get i)) with
         | none => .arr ν ν
         | some ρ => .arr ρ (.arr ν ν)))
    (hrTy : HasType r (Ty.arrMany (ys.map Var.ty) ν))
    (hBindersFresh :
      let wVars := (List.ofFn ws).filterMap id
      let vVars := List.ofFn vs
      (ys ++ wVars ++ vVars).Nodup ∧
      (∀ y ∈ ys, ∀ D ∈ Ds, y ∉ freeVarsFormula D) ∧
      (∀ z ∈ wVars ++ vVars, ∀ i, z ∉ freeVars (ss i)) ∧
      (∀ z ∈ ys ++ wVars, z ∉ freeVars r) ∧
      (∀ z ∈ wVars ++ vVars, ∀ D ∈ Ds, z ∉ freeVarsFormula D) ∧
      (∀ z ∈ wVars ++ vVars, ∀ G ∈ Gs, z ∉ freeVarsFormula G) ∧
      (∀ z ∈ ys ++ wVars ++ vVars,
        z = comp.var ∨ z ∉ freeVarsFormula comp.body))
    (h7 : ∀ j,
      Provable SysConfig.Z
        (Formula.impMany Ds (mrFormula ν comp (substBotWithX (Ds.get j)) (ts j))))
    (h8 : ∀ i,
      Provable SysConfig.Z
        (Formula.impMany Ds
          (.imp
            (mrFormula ν comp (substBotWithX (Gs.get i))
              (Realizer.ofOption ((ws i).map Term.var)
                (by simpa only [Option.isSome_map] using congrArg Option.isSome (hwsTy i))))
            (.imp
              (.imp (Gs.get i) (comp.apply (.var (vs i))))
              (comp.apply (applyGoalRealizer (ss i) (ws i) (.var (vs i))))))))
    (h9 : Provable SysConfig.Z
      (Formula.impMany Ds
        (Formula.allMany ys
          (Formula.impMany Gs (comp.apply (Term.appMany r (ys.map Term.var)))))))
    (hM : Derivable SysConfig.Z0 M (Formula.impMany Ds (goalImpliesBot ys Gs)))
    (hMClosed : freeAssumpVars M = [])
    (hMAdm : AdmissibleForExtraction ν dummy (substBotProof M)) :
    let s := buildGoalCombinatorTerm ys (List.ofFn ws) (List.ofFn ss) r
    ∃ p : Term,
      extractRaw ν dummy (substBotProof M) = some p ∧
      HasType (.app (applyOptTerms p (List.ofFn fun j => (ts j).toOption)) s) ν ∧
      Provable SysConfig.Z
        (Formula.impMany Ds
          (comp.apply (.app (applyOptTerms p (List.ofFn fun j => (ts j).toOption)) s))) := by
  let H := Formula.allMany ys (Formula.impMany (Gs.map substBotWithX) .varX)
  let K := Formula.imp H .varX
  let s := buildGoalCombinatorTerm ys (List.ofFn ws) (List.ofFn ss) r
  have hDsAllowed : ∀ D ∈ Ds, SysConfig.Z.allowsFormula D :=
    fun D hD ↦ ⟨(hDs D hD).1, .inr (hDs D hD).2⟩
  have hDX : ∀ A ∈ Ds.map substBotWithX, FormulaWellTyped A := by
    intro A hA
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hA
    exact ComputationalReduction.FormulaWellTyped.substBotWithX (hDs D hD).1
  have hGX : ∀ A ∈ Gs.map substBotWithX, FormulaWellTyped A := by
    intro A hA
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hA
    exact ComputationalReduction.FormulaWellTyped.substBotWithX (hGs G hG).1
  have hH : FormulaWellTyped H :=
    (ComputationalLogic.allows_allMany (sys := SysConfig.ZX) ys
      ⟨impMany_wellTyped _ .varX hGX .varX, .inl rfl⟩).1
  have hK : FormulaWellTyped K := .imp hH .varX
  have hTauH : tau ν H = some (goalType ν ys Gs) :=
    tau_allMany ν ys _ _ (tau_impMany ν (Gs.map substBotWithX) .varX ν rfl)
  have hTauK : tau ν K = some (.arr (goalType ν ys Gs) ν) := by
    simp only [K, tau, hTauH]
  have hTauP := tau_impMany ν (Ds.map substBotWithX) K _ hTauK
  obtain ⟨p, hpRaw, hpTy, hOriginalMR⟩ :=
    extracted_input_realizes ν dummy comp Ds Gs ys M hM hMClosed hMAdm
  let pR : Realizer (tau ν (Formula.impMany (Ds.map substBotWithX) K)) :=
    Realizer.cast hTauP.symm p
  have hpOption : pR.toOption = some p := Realizer.toOption_cast hTauP.symm p
  have hpRTy : pR.Typed := (Realizer.typed_cast hTauP.symm p).mpr hpTy
  have hFormula : substBotWithX (Formula.impMany Ds (goalImpliesBot ys Gs)) =
      Formula.impMany (Ds.map substBotWithX) K := by
    simp only [substBotWithX_impMany, substBotWithX_goalImpliesBot, goalImpliesX, K, H]
  have hPMR : Provable SysConfig.Z
      (mrFormula ν comp (Formula.impMany (Ds.map substBotWithX) K) pR) := by
    apply Provable.conv hOriginalMR
      (MrLogic.mr_allowed ν comp _ pR (impMany_wellTyped _ K hDX hK) hpRTy)
    apply hc (substBotWithX (Formula.impMany Ds (goalImpliesBot ys Gs)))
      (Formula.impMany (Ds.map substBotWithX) K) (by rw [hFormula]; exact .refl _)
    have hOld : (Realizer.cast (tau_input ν Ds Gs ys).symm p).toOption = some p :=
      Realizer.toOption_cast (tau_input ν Ds Gs ys).symm p
    rw [hOld, hpOption]
    exact .some (.refl p)
  let qR := applyImpMany ν Ds K pR ts
  have hqTy : qR.Typed := applyImpMany_typed ν Ds K pR ts hpRTy htsTy
  have hqOption : qR.toOption = some (applyOptTerms p (List.ofFn fun j ↦ (ts j).toOption)) :=
    applyImpMany_toOption ν Ds K pR ts p hpOption
  have hqMR : Provable SysConfig.Z (Formula.impMany Ds (mrFormula ν comp K qR)) :=
    applyImpMany_spec ν comp hc hs Ds Ds K pR ts hDsAllowed
      (fun D hD ↦ (hDs D hD).1) hK hpRTy htsTy (Provable.ctx_const hDsAllowed hPMR) h7
  let sR : Realizer (tau ν H) := Realizer.cast hTauH.symm s
  have hsOption : sR.toOption = some s := Realizer.toOption_cast hTauH.symm s
  have hsTy : sR.Typed := (Realizer.typed_cast hTauH.symm s).mpr
    (goalCombinator_typed ν ys Gs ws ss r hwsTy hssTy hrTy)
  have hExpanded := source_goal_matrix ν comp Ds Gs ys ws ss vs r hDs hGs hwsTy hvsTy hssTy hrTy
    hBindersFresh h8 h9
  have hAbstraction : FormulaBetaREq (mrFormula ν comp H sR)
      (Formula.allMany ys (ComputationalLogic.quantifiedMatrix
        (List.ofFn fun i ↦ (ws i, goalPremise ν comp (Gs.get i) (ws i) (hwsTy i)))
        (comp.apply ((List.zip (List.ofFn ss) (List.ofFn ws)).foldr
          (fun (s, w) acc ↦ applyGoalRealizer s w acc)
          (Term.appMany r (ys.map Term.var)))))) := by
    apply mr_goalCombinator ν comp hc hs ys Gs ws ss r hwsTy sR hsOption
    · intro w hw G hG
      exact hBindersFresh.2.2.2.2.2.1 w (List.mem_append_left _ hw) G hG
    · intro w hw
      apply hBindersFresh.2.2.2.2.2.2 w
      have h : w ∈ (ys ++ (List.ofFn ws).filterMap id) ++ List.ofFn vs :=
        List.mem_append_left _ (List.mem_append_right _ hw)
      simpa only [List.append_assoc] using h
    · intro y hy
      apply hBindersFresh.2.2.2.2.2.2 y
      have h : y ∈ (ys ++ (List.ofFn ws).filterMap id) ++ List.ofFn vs :=
        List.mem_append_left _ (List.mem_append_left _ hy)
      simpa only [List.append_assoc] using h
  have hsMR : Provable SysConfig.Z (Formula.impMany Ds (mrFormula ν comp H sR)) :=
    ComputationalLogic.ctx_conv hDsAllowed (MrLogic.mr_allowed ν comp H sR hH hsTy)
      hAbstraction.symm hExpanded
  let outputR := Realizer.applyImp ν H .varX qR sR
  have hOutTy : outputR.Typed := Realizer.applyImp_typed ν H .varX qR sR hqTy hsTy
  have hImp := MrLogic.mr_imp_elim ν comp hc hs H .varX qR sR hH .varX hqTy hsTy
  have hOut : Provable SysConfig.Z (Formula.impMany Ds (mrFormula ν comp .varX outputR)) :=
    Provable.ctx_mp hDsAllowed (MrLogic.mr_allowed ν comp H sR hH hsTy)
      (MrLogic.mr_allowed ν comp .varX outputR .varX hOutTy)
      (Provable.ctx_mp hDsAllowed (MrLogic.mr_allowed ν comp K qR hK hqTy)
        ((MrLogic.mr_allowed ν comp H sR hH hsTy).imp
          (MrLogic.mr_allowed ν comp .varX outputR .varX hOutTy))
        (Provable.ctx_const hDsAllowed hImp) hqMR) hsMR
  have hOutOption : outputR.toOption =
      some (.app (applyOptTerms p (List.ofFn fun j ↦ (ts j).toOption)) s) := by
    rw [Realizer.applyImp_toOption, hqOption, hsOption]
  have hOutEq : outputR = .app (applyOptTerms p (List.ofFn fun j ↦ (ts j).toOption)) s :=
    Option.some.inj hOutOption
  rw [mrFormula.eq_def ν comp .varX outputR, hOutEq] at hOut
  exact ⟨p, hpRaw,
    .app (applyOptTerms_typed ν Ds ts htsTy p _ hpTy)
      (goalCombinator_typed ν ys Gs ws ss r hwsTy hssTy hrTy), hOut⟩

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


/- Local checked proof module: Solution51 -/

open BBS2002 BBS2002.V2

theorem solution
    (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    (Ds Gs : List Formula) (ys : List Var)
    (ts : (j : Fin Ds.length) → Realizer (tau ν (substBotWithX (Ds.get j))))
    (ws : Fin Gs.length → Option Var) (ss : Fin Gs.length → Term)
    (vs : Fin Gs.length → Var) (r : Term) (M : ProofTerm)
    (hDs : ∀ D ∈ Ds, FormulaWellTyped D ∧ isLFormula D = true)
    (hGs : ∀ G ∈ Gs, FormulaWellTyped G ∧ isLFormula G = true)
    (htsTy : ∀ j, (ts j).Typed)
    (hwsTy : ∀ i, (ws i).map Var.ty = tau ν (substBotWithX (Gs.get i)))
    (hvsTy : ∀ i, (vs i).ty = ν)
    (hssTy : ∀ i,
      HasType (ss i)
        (match tau ν (substBotWithX (Gs.get i)) with
         | none => .arr ν ν
         | some ρ => .arr ρ (.arr ν ν)))
    (hrTy : HasType r (Ty.arrMany (ys.map Var.ty) ν))
    (hBindersFresh :
      let wVars := (List.ofFn ws).filterMap id
      let vVars := List.ofFn vs
      (ys ++ wVars ++ vVars).Nodup ∧
      (∀ y ∈ ys, ∀ D ∈ Ds, y ∉ freeVarsFormula D) ∧
      (∀ z ∈ wVars ++ vVars, ∀ i, z ∉ freeVars (ss i)) ∧
      (∀ z ∈ ys ++ wVars, z ∉ freeVars r) ∧
      (∀ z ∈ wVars ++ vVars, ∀ D ∈ Ds, z ∉ freeVarsFormula D) ∧
      (∀ z ∈ wVars ++ vVars, ∀ G ∈ Gs, z ∉ freeVarsFormula G) ∧
      (∀ z ∈ ys ++ wVars ++ vVars,
        z = comp.var ∨ z ∉ freeVarsFormula comp.body))
    (h7 : ∀ j,
      Provable SysConfig.Z
        (Formula.impMany Ds (mrFormula ν comp (substBotWithX (Ds.get j)) (ts j))))
    (h8 : ∀ i,
      Provable SysConfig.Z
        (Formula.impMany Ds
          (.imp
            (mrFormula ν comp (substBotWithX (Gs.get i))
              (Realizer.ofOption ((ws i).map Term.var)
                (by simpa only [Option.isSome_map] using congrArg Option.isSome (hwsTy i))))
            (.imp
              (.imp (Gs.get i) (comp.apply (.var (vs i))))
              (comp.apply (applyGoalRealizer (ss i) (ws i) (.var (vs i))))))))
    (h9 : Provable SysConfig.Z
      (Formula.impMany Ds
        (Formula.allMany ys
          (Formula.impMany Gs (comp.apply (Term.appMany r (ys.map Term.var)))))))
    (hM : Derivable SysConfig.Z0 M (Formula.impMany Ds (goalImpliesBot ys Gs)))
    (hMClosed : freeAssumpVars M = [])
    (hMAdm : AdmissibleForExtraction ν dummy (substBotProof M)) :
    let s := buildGoalCombinatorTerm ys (List.ofFn ws) (List.ofFn ss) r
    ∃ p : Term,
      extractRaw ν dummy (substBotProof M) = some p ∧
      HasType (.app (applyOptTerms p (List.ofFn fun j => (ts j).toOption)) s) ν ∧
      Provable SysConfig.Z
        (Formula.impMany Ds
          (comp.apply (.app (applyOptTerms p (List.ofFn fun j => (ts j).toOption)) s))) := by
  exact theorem_5_1_of_mr_laws ν dummy comp
    (mrFormula_compatible ν comp) (mrFormula_substitution ν comp)
    Ds Gs ys ts ws ss vs r M hDs hGs htsTy hwsTy hvsTy hssTy hrTy
    hBindersFresh h7 h8 h9 hM hMClosed hMAdm

