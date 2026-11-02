-- Prove2me | solution 1 for BBS2002.V2.corollary_5_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:49:15.551911+00:00
-- url     : https://prove2.me/submissions/32c9a598-6f4c-425f-98c7-70e2016c00ec

import Definitions.Def_BBS2002_V2_Realizability
import Theorems.Thm_BBS2002_V2_theorem_5_1
import Theorems.Thm_BBS2002_V2_theorem_5_2

/-!
Corollary 5.3 reduced to the replacement Theorems 5.1 and 5.2.
The auxiliary lemmas below are proved in this file. The imported theorems
are the only open mathematical dependencies of the reduction.
-/


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


namespace BBS2002.V2

/-- The single-goal combinator used in Corollary 5.3 has the input type expected by
the extracted classical proof. The realizer `s` may retain the goal parameter `y`. -/
theorem singleGoalCombinator_type
    (y : Var) (τ : Option Ty) (w : Option Var) (hw : w.map Var.ty = τ)
    (s : Term)
    (hs : HasType s (match τ with
      | none => .arr y.ty y.ty
      | some ρ => .arr ρ (.arr y.ty y.ty))) :
    HasType (buildGoalCombinatorTerm [y] [w] [s] (.lam y (.var y)))
      (.arr y.ty (match τ with
        | none => y.ty
        | some ρ => .arr ρ y.ty)) := by
  cases w with
  | none =>
      cases hw
      exact .lam y (.app hs (.app (.lam y (.var y)) (.var y)))
  | some w =>
      cases hw
      exact .lam y (.lam w (.app (.app hs (.var w)) (.app (.lam y (.var y)) (.var y))))

end BBS2002.V2

namespace BBS2002.V2.RootReduction

theorem IsDefinite_IsGoal_wf_and_L (A : Formula) :
    (IsDefiniteFormula A → FormulaWellTyped A ∧ isLFormula A = true) ∧
    (IsGoalFormula A → FormulaWellTyped A ∧ isLFormula A = true) := by
  induction A with
  | bot =>
      exact ⟨fun _ => ⟨.bot, rfl⟩, fun _ => ⟨.bot, rfl⟩⟩
  | varX =>
      refine ⟨fun hD => ?_, fun hG => ?_⟩
      · cases hD with | atom hAt _ => cases hAt
      · cases hG with | atom hAt _ => cases hAt
  | atom t =>
      refine ⟨fun hD => ?_, fun hG => ?_⟩
      · cases hD with | atom _ hwf => exact ⟨hwf, rfl⟩
      · cases hG with | atom _ hwf => exact ⟨hwf, rfl⟩
  | imp B C ihB ihC =>
      refine ⟨fun hD => ?_, fun hG => ?_⟩
      · cases hD with
        | atom hAt _ => cases hAt
        | imp hGB hDC _ =>
            have hB := ihB.2 hGB
            have hC := ihC.1 hDC
            exact ⟨.imp hB.1 hC.1, by simp [isLFormula, hB.2, hC.2]⟩
      · cases hG with
        | atom hAt _ => cases hAt
        | imp hDB hGC _ =>
            have hB := ihB.1 hDB
            have hC := ihC.2 hGC
            exact ⟨.imp hB.1 hC.1, by simp [isLFormula, hB.2, hC.2]⟩
  | all x B ihB =>
      refine ⟨fun hD => ?_, fun hG => ?_⟩
      · cases hD with
        | atom hAt _ => cases hAt
        | all _ hDB =>
            have hB := ihB.1 hDB
            exact ⟨.all x hB.1, by simp [isLFormula, hB.2]⟩
      · cases hG with
        | atom hAt _ => cases hAt
        | all _ hGB _ =>
            have hB := ihB.2 hGB
            exact ⟨.all x hB.1, by simp [isLFormula, hB.2]⟩

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

theorem allows_imp_right {sys : SysConfig} {A B : Formula}
    (h : sys.allowsFormula (.imp A B)) : sys.allowsFormula B := by
  rcases h with ⟨ht, hl⟩
  cases ht with
  | imp ha hb =>
      refine ⟨hb, ?_⟩
      rcases hl with h | h
      · exact .inl h
      · exact .inr (Bool.and_eq_true_iff.mp h).2

theorem allows_all_body {sys : SysConfig} {x : Var} {A : Formula}
    (h : sys.allowsFormula (.all x A)) : sys.allowsFormula A := by
  rcases h with ⟨ht, hl⟩
  cases ht with
  | all _ ha => exact ⟨ha, hl⟩

theorem derivable_allowed {sys : SysConfig} {M : ProofTerm} {A : Formula}
    (h : Derivable sys M A) : sys.allowsFormula A := by
  induction h with
  | assump _ ha => exact ha
  | indNat n A hn ha =>
      exact (ha.substFormula n (hn ▸ HasType.const .zero)).imp
        ((ha.imp (ha.substFormula n
          (hn.symm ▸ .app (HasType.const .succ) (hn ▸ HasType.var n)))).all n |>.imp (ha.all n))
  | indBool p A hp ha =>
      exact (ha.substFormula p (hp ▸ HasType.const .trueConst)).imp
        ((ha.substFormula p (hp ▸ HasType.const .falseConst)).imp (ha.all p))
  | axTrue => exact .trueAtom _
  | axFalse _ ha => exact (SysConfig.allowsFormula.falseAtom _).imp ha
  | efq _ _ ha => exact (SysConfig.allowsFormula.bot _).imp ha
  | lamAssump _ ha _ ih => exact ha.imp ih
  | appAssump _ _ ih _ => exact allows_imp_right ih
  | lamTerm x _ _ ih => exact ih.all x
  | appTerm t ht _ ih => exact (allows_all_body ih).substFormula _ ht
  | conv _ ha _ _ => exact ha

theorem id_redex_fv (y : Var) :
    freeVarOccurrences (.app (.lam y (.var y)) (.var y)) = [y] := by
  simp [freeVarOccurrences]

theorem term_subst_id_redex (t : Term) (y : Var) :
    BetaREq (substTerm t y (.app (.lam y (.var y)) (.var y))) t := by
  induction t with
  | var x =>
      rw [substTerm.eq_def]
      by_cases hxy : x = y
      · subst x
        simpa using BetaREq.of_conv (.beta y (.var y) (.var y))
      · simpa only [beq_eq_false_iff_ne.mpr hxy, Bool.false_eq_true, ↓reduceIte]
          using BetaREq.refl (.var x)
  | const c => rw [substTerm.eq_def]; exact .refl _
  | app r s ihr ihs => rw [substTerm.eq_def]; exact .app ihr ihs
  | lam x t ih =>
      rw [substTerm.eq_def]
      by_cases hxy : x = y
      · subst x
        simp only [beq_self_eq_true, ↓reduceIte]
        exact .refl _
      · simp only [beq_eq_false_iff_ne.mpr hxy, Bool.false_eq_true, ↓reduceIte,
          id_redex_fv, List.mem_singleton, hxy]
        exact .lam x ih

theorem formula_subst_id_redex (A : Formula) (y : Var) :
    FormulaBetaREq (substFormula A y (.app (.lam y (.var y)) (.var y))) A := by
  induction A with
  | bot => rw [substFormula.eq_def]; exact .bot
  | varX => rw [substFormula.eq_def]; exact .varX
  | atom t => rw [substFormula.eq_def]; exact .atom (term_subst_id_redex t y)
  | imp A B ihA ihB => rw [substFormula.eq_def]; exact .imp ihA ihB
  | all x A ih =>
      rw [substFormula.eq_def]
      by_cases hxy : x = y
      · subst x
        simp only [beq_self_eq_true, ↓reduceIte]
        exact .refl _
      · simp only [beq_eq_false_iff_ne.mpr hxy, Bool.false_eq_true, ↓reduceIte,
          id_redex_fv, List.mem_singleton, hxy]
        exact .all x ih

theorem singleGoalCombinator_support (y : Var) (w : Option Var) (s : Term) (G : Formula)
    (hs : ∀ x ∈ freeVars s, x ∈ freeVarsFormula G) :
    ∀ x ∈ freeVars (buildGoalCombinatorTerm [y] [w] [s] (.lam y (.var y))),
      x ∈ freeVarsFormula G ∧ x ≠ y := by
  intro x hx
  cases w with
  | none =>
      simp [buildGoalCombinatorTerm, Term.appMany, Term.lamMany, optLamVars,
        applyGoalRealizer, freeVars, freeVarOccurrences] at hx
      exact ⟨hs x (by simpa [freeVars] using hx.1), hx.2⟩
  | some w =>
      simp [buildGoalCombinatorTerm, Term.appMany, Term.lamMany, optLamVars,
        applyGoalRealizer, freeVars, freeVarOccurrences] at hx
      exact ⟨hs x (by simpa [freeVars] using hx.1), hx.2.1⟩

end BBS2002.V2.RootReduction

open BBS2002 BBS2002.V2 BBS2002.V2.RootReduction

theorem solution
    (Ds : List Formula) (G : Formula) (y : Var) (dummy : Term)
    (hDs : ∀ D ∈ Ds, IsDefiniteFormula D)
    (hG : IsGoalFormula G)
    (hyDs : ∀ D ∈ Ds, y ∉ freeVarsFormula D)
    (hDummyTy : HasType dummy y.ty)
    (hDummyClosed : IsClosedTerm dummy) :
    ∃ (ts : (j : Fin Ds.length) → Realizer (tau y.ty (substBotWithX (Ds.get j))))
      (s : Term),
      (∀ j, (ts j).Typed) ∧
      (∀ j, ∀ t₀ ∈ (ts j).toOption, ∀ x ∈ freeVars t₀, x ∈ freeVarsFormula (Ds.get j)) ∧
      HasType s
        (.arr y.ty (match tau y.ty (substBotWithX G) with
          | none => y.ty
          | some ρ => .arr ρ y.ty)) ∧
      (∀ x ∈ freeVars s, x ∈ freeVarsFormula G ∧ x ≠ y) ∧
      (∀ M : ProofTerm,
        Derivable SysConfig.Z0 M (Formula.impMany Ds (goalImpliesBot [y] [G])) →
        freeAssumpVars M = [] →
        AdmissibleForExtraction y.ty dummy (substBotProof M) →
        ∃ p : Term,
          extractRaw y.ty dummy (substBotProof M) = some p ∧
          let output := .app (applyOptTerms p (List.ofFn (fun j ↦ (ts j).toOption))) s
          HasType output y.ty ∧
          Provable SysConfig.Z (Formula.impMany Ds (substFormula G y output))) := by
  classical
  have hd : ∀ D ∈ Ds, FormulaWellTyped D ∧ isLFormula D = true :=
    fun D hD ↦ (IsDefinite_IsGoal_wf_and_L D).1 (hDs D hD)
  have hg := (IsDefinite_IsGoal_wf_and_L G).2 hG
  have htD (j : Fin Ds.length) :=
    (theorem_5_2 y.ty dummy hDummyTy hDummyClosed (Ds.get j) G
      (hDs _ (List.get_mem ..)) hG).1
  let ts (j : Fin Ds.length) := Classical.choose (htD j)
  have hts (j : Fin Ds.length) := Classical.choose_spec (htD j)
  obtain ⟨sG, hsTy, hsSupport, hsSpec⟩ :=
    (theorem_5_2 y.ty dummy hDummyTy hDummyClosed .bot G (.atom rfl .bot) hG).2
  let params := Ds.flatMap freeVarsFormula ++ freeVarsFormula G ++ [y]
  obtain ⟨wv, hwvTy, hwvFresh⟩ :=
    exists_fresh_var params ((tau y.ty (substBotWithX G)).getD y.ty)
  obtain ⟨vv, hvvTy, hvvFresh⟩ := exists_fresh_var (wv :: params) y.ty
  let w := (tau y.ty (substBotWithX G)).map (fun _ ↦ wv)
  have hwTy : w.map Var.ty = tau y.ty (substBotWithX G) := by
    cases htau : tau y.ty (substBotWithX G) with
    | none => simp [w, htau]
    | some ρ => simpa [w, htau] using hwvTy
  have hComb : HasType (buildGoalCombinatorTerm [y] [w] [sG] (.lam y (.var y)))
      (.arr y.ty (match tau y.ty (substBotWithX G) with
        | none => y.ty | some ρ => .arr ρ y.ty)) := by
    cases hτ : tau y.ty (substBotWithX G) with
    | none =>
        simp only [hτ] at hsTy hwTy
        exact singleGoalCombinator_type y none w hwTy sG hsTy
    | some ρ =>
        simp only [hτ] at hsTy hwTy
        exact singleGoalCombinator_type y (some ρ) w hwTy sG hsTy
  refine ⟨ts, buildGoalCombinatorTerm [y] [w] [sG] (.lam y (.var y)),
    (fun j ↦ (hts j).1), (fun j ↦ (hts j).2.1), hComb,
    singleGoalCombinator_support y w sG G hsSupport, fun M hM hMClosed hMAdm ↦ ?_⟩
  let comp : CompTerm y.ty := ⟨y, G, rfl, hg.2, hg.1⟩
  have hDsAllowed : ∀ D ∈ Ds, SysConfig.Z.allowsFormula D :=
    fun D hD ↦ ⟨(hd D hD).1, .inr (hd D hD).2⟩
  have h7 (j : Fin Ds.length) : Provable SysConfig.Z
      (Formula.impMany Ds (mrFormula y.ty comp (substBotWithX (Ds.get j)) (ts j))) :=
    Provable.ctx_mp hDsAllowed (hDsAllowed _ (List.get_mem ..))
      (allows_imp_right (derivable_allowed ((hts j).2.2 comp).choose_spec.1))
      (Provable.ctx_const hDsAllowed ((hts j).2.2 comp))
      (Provable.ctx_hyp hDsAllowed (List.get_mem ..))
  have hwv : (∀ D ∈ Ds, wv ∉ freeVarsFormula D) ∧
      wv ∉ freeVarsFormula G ∧ wv ≠ y := by
    simpa [params, List.mem_flatMap, and_assoc] using hwvFresh
  have hvv : vv ≠ wv ∧ (∀ D ∈ Ds, vv ∉ freeVarsFormula D) ∧
      vv ∉ freeVarsFormula G ∧ vv ≠ y := by
    simpa [params, List.mem_flatMap, and_assoc] using hvvFresh
  have hwMem : ∀ x ∈ w, x = wv := by
    cases hτ : tau y.ty (substBotWithX G) <;> simp [w, hτ]
  have h8 := Provable.ctx_const hDsAllowed (hsSpec comp w vv hvvTy hwTy
    (fun x hx ↦ (hwMem x hx).symm ▸ ⟨Ne.symm hvv.1, hwv.2.1, .inr hwv.2.1⟩)
    hvv.2.2.1 (.inr hvv.2.2.1))
  have hGAllowed : SysConfig.Z.allowsFormula G := ⟨hg.1, .inr hg.2⟩
  have h9 : Provable SysConfig.Z
      (Formula.impMany Ds (Formula.allMany [y] (Formula.impMany [G]
        (comp.apply (Term.appMany (.lam y (.var y)) ([y].map Term.var)))))) :=
    Provable.ctx_const hDsAllowed (Provable.all_intro y
      (Provable.conv (Provable.id hGAllowed)
        (hGAllowed.imp (hGAllowed.substFormula y (.app (.lam y (.var y)) (.var y))))
        (.imp (.refl G) (formula_subst_id_redex G y).symm)))
  have hMain := theorem_5_1 y.ty dummy comp Ds [G] [y] ts
    (fun _ ↦ w) (fun _ ↦ sG) (fun _ ↦ vv) (.lam y (.var y)) M hd
    (fun A hA ↦ (List.mem_singleton.mp hA).symm ▸ hg)
    (fun j ↦ (hts j).1) (fun i ↦ by simpa using hwTy)
    (fun _ ↦ hvvTy) (fun i ↦ by
      have hi : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      subst i
      split <;> rename_i hτ <;>
        change tau y.ty (substBotWithX G) = _ at hτ <;>
        simpa only [hτ] using hsTy)
    (.lam y (.var y)) ?_ h7 (fun i ↦ by
      have hi : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      subst i
      exact h8) h9 hM hMClosed hMAdm
  · simpa [List.ofFn_succ, comp, CompTerm.apply] using hMain
  · simp only [List.ofFn_succ, List.ofFn_zero]
    have hsFresh : wv ∉ freeVars sG ∧ vv ∉ freeVars sG :=
      ⟨fun h ↦ hwv.2.1 (hsSupport _ h), fun h ↦ hvv.2.2.1 (hsSupport _ h)⟩
    have hId : freeVars (.lam y (.var y)) = [] := by simp [freeVars, freeVarOccurrences]
    cases hτ : tau y.ty (substBotWithX G) <;>
      simp [w, hτ, comp, hsFresh.1, hsFresh.2, hId, hwv.2.1,
        hwv.2.2, Ne.symm hwv.2.2, Ne.symm hvv.1,
        hvv.2.2.1, hvv.2.2.2, Ne.symm hvv.2.2.2]
    · exact ⟨hyDs, hvv.2.1⟩
    · exact ⟨hyDs, hwv.1, hvv.2.1⟩
