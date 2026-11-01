-- Prove2me | solution 1 for BBS2002.lemmas_2_1_to_2_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:07:32.623721+00:00
-- url     : https://prove2.me/submissions/85581098-c051-4137-a38d-d45bfe64d1ab

import Definitions.Def_BBS2002_Arithmetic

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

/-! ## Section 2, Lemma 2.1 -/

/-- Replace `⊥` with `F := atom(false)` throughout a `Z^X`-derivation `M` (turning `efq_A` into `ax_{false,A^F}`). -/
def substBotFalseProof : ProofTerm → ProofTerm
  | .assump u => .assump ⟨u.id, substBotWithFalse u.formula⟩
  | .indNat n A => .indNat n (substBotWithFalse A)
  | .indBool p A => .indBool p (substBotWithFalse A)
  | .axTrue => .axTrue
  | .axFalse A => .axFalse (substBotWithFalse A)
  | .efq A => .axFalse (substBotWithFalse A)
  | .lamAssump u M => .lamAssump ⟨u.id, substBotWithFalse u.formula⟩ (substBotFalseProof M)
  | .appAssump M N => .appAssump (substBotFalseProof M) (substBotFalseProof N)
  | .lamTerm x M => .lamTerm x (substBotFalseProof M)
  | .appTerm M t => .appTerm (substBotFalseProof M) t

@[simp] theorem substBotWithFalse_bot : substBotWithFalse .bot = Formula.falseAtom := rfl
@[simp] theorem substBotWithFalse_varX : substBotWithFalse .varX = .varX := rfl
@[simp] theorem substBotWithFalse_atom (t : Term) : substBotWithFalse (.atom t) = .atom t := rfl
@[simp] theorem substBotWithFalse_imp (B C : Formula) :
    substBotWithFalse (.imp B C) = .imp (substBotWithFalse B) (substBotWithFalse C) := rfl
@[simp] theorem substBotWithFalse_all (x : Var) (B : Formula) :
    substBotWithFalse (.all x B) = .all x (substBotWithFalse B) := rfl

@[simp]
theorem maxVarIdFormula_substBotWithFalse (A : Formula) :
    maxVarIdFormula (substBotWithFalse A) = maxVarIdFormula A := by
  induction A with
  | bot | varX | atom _ => rfl
  | imp B C ihB ihC => simp [maxVarIdFormula, ihB, ihC]
  | all x B ih => simp [maxVarIdFormula, ih]

@[simp]
theorem allVarsFormula_substBotWithFalse (A : Formula) :
    allVarsFormula (substBotWithFalse A) = allVarsFormula A := by
  induction A with
  | bot | varX | atom _ => rfl
  | imp B C ihB ihC => simp [allVarsFormula, ihB, ihC]
  | all x B ih => simp [allVarsFormula, ih]

@[simp]
theorem freeVarsFormula_substBotWithFalse (A : Formula) :
    freeVarsFormula (substBotWithFalse A) = freeVarsFormula A := by
  induction A with
  | bot | varX | atom _ => rfl
  | imp B C ihB ihC => simp [freeVarsFormula, ihB, ihC]
  | all x B ih => simp [freeVarsFormula, ih]

@[simp]
theorem renameFreeVarFormula_substBotWithFalse (A : Formula) (x y : Var) :
    renameFreeVarFormula (substBotWithFalse A) x y =
      substBotWithFalse (renameFreeVarFormula A x y) := by
  induction A with
  | bot | varX | atom _ => rfl
  | imp B C ihB ihC => simp [renameFreeVarFormula, ihB, ihC]
  | all v B ih =>
      simp only [substBotWithFalse_all, renameFreeVarFormula]
      split <;> simp [ih]

theorem substFormula_substBotWithFalse (A : Formula) (x : Var) (t : Term) :
    substFormula (substBotWithFalse A) x t = substBotWithFalse (substFormula A x t) := by
  match A with
  | .bot | .varX | .atom _ =>
      simp
  | .imp B C =>
      simp [substFormula_substBotWithFalse B x t, substFormula_substBotWithFalse C x t]
  | .all v B =>
      simp only [substBotWithFalse_all]
      rw [substFormula.eq_def, substFormula.eq_def]
      by_cases hvx : v = x
      · subst hvx; simp
      · have hvxb : (v == x) = false := beq_eq_false_iff_ne.mpr hvx
        simp only [hvxb, Bool.false_eq_true, ↓reduceIte, maxVarIdFormula_substBotWithFalse]
        split
        · let freshId := Nat.max (maxVarIdFormula B) (Nat.max (maxVarIdTerm t) x.id) + 1
          let v' : Var := ⟨freshId, v.ty⟩
          rw [renameFreeVarFormula_substBotWithFalse]
          have ih := substFormula_substBotWithFalse (renameFreeVarFormula B v v') x t
          simpa using ih
        · have ih := substFormula_substBotWithFalse B x t
          simpa using ih
termination_by formulaSize A
decreasing_by
  all_goals
    simp_wf
    simp [formulaSize, renameFreeVarFormula_size]
    try omega

theorem FormulaBetaREq.substBotWithFalse {A B : Formula} (h : FormulaBetaREq A B) :
    FormulaBetaREq (BBS2002.substBotWithFalse A) (BBS2002.substBotWithFalse B) := by
  induction h with
  | refl C => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | bot => exact .refl _
  | varX => exact .varX
  | atom hstep => exact .atom hstep
  | imp _ _ ih1 ih2 => exact .imp ih1 ih2
  | all x _ ih => exact .all x ih
  | all_rename x y C hty hfresh =>
      simp only [substBotWithFalse_all, ← renameFreeVarFormula_substBotWithFalse]
      apply FormulaBetaREq.all_rename x y (BBS2002.substBotWithFalse C) hty
      simpa [allVarsFormula_substBotWithFalse] using hfresh

theorem mem_freeAssumpVars_substBotFalseProof {M : ProofTerm} {v : AssumpVar}
    (hv : v ∈ freeAssumpVars (substBotFalseProof M)) :
    ∃ u ∈ freeAssumpVars M, v = ⟨u.id, substBotWithFalse u.formula⟩ := by
  induction M generalizing v with
  | assump u =>
      simp only [substBotFalseProof, freeAssumpVars, List.mem_singleton] at hv ⊢
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

theorem SysConfig.allowsFormula.substBotWithFalse_ZX0 {A : Formula}
    (hA : SysConfig.ZX.allowsFormula A) :
    SysConfig.ZX0.allowsFormula (BBS2002.substBotWithFalse A) :=
  ⟨hA.1.substBotWithFalse, .inl rfl⟩

theorem Derivable.substBotFalseProof {M : ProofTerm} {A : Formula}
    (h : Derivable SysConfig.ZX M A) :
    Derivable SysConfig.ZX0 (BBS2002.substBotFalseProof M) (substBotWithFalse A) := by
  induction h with
  | assump u hu =>
      exact .assump ⟨u.id, substBotWithFalse u.formula⟩ hu.substBotWithFalse_ZX0
  | indNat n A hn hA =>
      have h0 := Derivable.indNat (sys := SysConfig.ZX0) n (substBotWithFalse A) hn
        hA.substBotWithFalse_ZX0
      simpa [BBS2002.substBotFalseProof, indNatFormula, substFormula_substBotWithFalse] using h0
  | indBool p A hp hA =>
      have h0 := Derivable.indBool (sys := SysConfig.ZX0) p (substBotWithFalse A) hp
        hA.substBotWithFalse_ZX0
      simpa [BBS2002.substBotFalseProof, indBoolFormula, substFormula_substBotWithFalse] using h0
  | axTrue =>
      exact .axTrue
  | axFalse A hA =>
      exact .axFalse (substBotWithFalse A) hA.substBotWithFalse_ZX0
  | efq A _ hA =>
      exact .axFalse (substBotWithFalse A) hA.substBotWithFalse_ZX0
  | lamAssump u hu _ ih =>
      exact .lamAssump ⟨u.id, substBotWithFalse u.formula⟩ hu.substBotWithFalse_ZX0 ih
  | appAssump _ _ ih1 ih2 =>
      exact .appAssump ih1 ih2
  | lamTerm x hfresh _ ih =>
      refine .lamTerm x ?_ ih
      intro v hv
      rcases mem_freeAssumpVars_substBotFalseProof hv with ⟨u, hu, rfl⟩
      simpa [freeVarsFormula_substBotWithFalse] using hfresh u hu
  | appTerm t ht _ ih =>
      rw [← substFormula_substBotWithFalse]
      exact .appTerm t ht ih
  | conv _ hB heq ih =>
      exact .conv ih hB.substBotWithFalse_ZX0 heq.substBotWithFalse

theorem Derivable.ZX0_to_ZX {M : ProofTerm} {A : Formula}
    (h : Derivable SysConfig.ZX0 M A) :
    Derivable SysConfig.ZX M A := by
  induction h with
  | assump u hu => exact .assump u ⟨hu.1, .inl rfl⟩
  | indNat n A hn hA => exact .indNat n A hn ⟨hA.1, .inl rfl⟩
  | indBool p A hp hA => exact .indBool p A hp ⟨hA.1, .inl rfl⟩
  | axTrue => exact .axTrue
  | axFalse A hA => exact .axFalse A ⟨hA.1, .inl rfl⟩
  | efq A hEfq _ => cases hEfq
  | lamAssump u hu _ ih => exact .lamAssump u ⟨hu.1, .inl rfl⟩ ih
  | appAssump _ _ ih1 ih2 => exact .appAssump ih1 ih2
  | lamTerm x hfresh _ ih => exact .lamTerm x hfresh ih
  | appTerm t ht _ ih => exact .appTerm t ht ih
  | conv _ hB heq ih => exact .conv ih ⟨hB.1, .inl rfl⟩ heq

theorem Provable.ZX0_to_ZX {A : Formula} (h : Provable SysConfig.ZX0 A) :
    Provable SysConfig.ZX A := by
  rcases h with ⟨M, hM, hMC⟩
  exact ⟨M, hM.ZX0_to_ZX, hMC⟩

theorem Provable.substBotWithFalse_equiv (A : Formula) (hA : FormulaWellTyped A) :
    Provable SysConfig.ZX (.imp A (substBotWithFalse A)) ∧
    Provable SysConfig.ZX (.imp (substBotWithFalse A) A) := by
  induction hA with
  | bot =>
      refine ⟨⟨.efq Formula.falseAtom, .efq Formula.falseAtom rfl (.falseAtom _), rfl⟩,
        ⟨.axFalse .bot, .axFalse .bot (.bot _), rfl⟩⟩
  | varX =>
      have h : SysConfig.ZX.allowsFormula .varX := ⟨.varX, .inl rfl⟩
      exact ⟨Provable.id h, Provable.id h⟩
  | atom ht =>
      have h : SysConfig.ZX.allowsFormula (.atom _) := ⟨.atom ht, .inl rfl⟩
      exact ⟨Provable.id h, Provable.id h⟩
  | imp hB hC ihB ihC =>
      have hBa : SysConfig.ZX.allowsFormula _ := ⟨hB, .inl rfl⟩
      have hBFa : SysConfig.ZX.allowsFormula _ := ⟨hB.substBotWithFalse, .inl rfl⟩
      have hCa : SysConfig.ZX.allowsFormula _ := ⟨hC, .inl rfl⟩
      have hCFa : SysConfig.ZX.allowsFormula _ := ⟨hC.substBotWithFalse, .inl rfl⟩
      exact ⟨Provable.imp_congr hBa hBFa hCa hCFa ihB.2 ihC.1,
        Provable.imp_congr hBFa hBa hCFa hCa ihB.1 ihC.2⟩
  | all x hB ih =>
      have hBa : SysConfig.ZX.allowsFormula _ := ⟨hB, .inl rfl⟩
      have hBFa : SysConfig.ZX.allowsFormula _ := ⟨hB.substBotWithFalse, .inl rfl⟩
      exact ⟨Provable.all_congr x hBa hBFa ih.1,
        Provable.all_congr x hBFa hBa ih.2⟩

theorem lemma_2_1 (A : Formula) (hA : FormulaWellTyped A) :
    Provable SysConfig.ZX A ↔ Provable SysConfig.ZX0 (substBotWithFalse A) := by
  constructor
  · rintro ⟨M, hM, hMC⟩
    refine ⟨substBotFalseProof M, hM.substBotFalseProof, ?_⟩
    apply freeAssumpVars_eq_nil_of_forall_not_mem
    intro v hv
    rcases mem_freeAssumpVars_substBotFalseProof hv with ⟨u, hu, _⟩
    rw [hMC] at hu
    cases hu
  · intro h
    exact Provable.mp (Provable.substBotWithFalse_equiv A hA).2 h.ZX0_to_ZX

/-! ## Section 2, Lemma 2.2 (Stability) -/

theorem not_mem_freeVarsFormula_dneg_all (x : Var) (B : Formula) :
    x ∉ freeVarsFormula (Formula.dneg (.all x B)) := by
  simp [Formula.dneg, Formula.neg, freeVarsFormula]

theorem lemma_2_2_stability (A : Formula) (hA : FormulaWellTyped A) (hL : isLFormula A = true) :
    Provable SysConfig.Z (.imp (Formula.dneg A) A) := by
  induction hA with
  | bot =>
      have hBot : SysConfig.Z.allowsFormula .bot := .bot _
      let Γ : List Formula := [Formula.dneg .bot]
      have hΓ : ∀ D ∈ Γ, SysConfig.Z.allowsFormula D := by
        intro D hD; simp only [Γ, List.mem_singleton] at hD; subst hD; exact hBot.dneg
      have hHyp : Provable SysConfig.Z (Formula.impMany Γ (.imp (Formula.neg .bot) .bot)) :=
        Provable.ctx_hyp hΓ (List.Mem.head _)
      have hId : Provable SysConfig.Z (Formula.impMany Γ (Formula.neg .bot)) :=
        Provable.ctx_const hΓ (Provable.id hBot)
      exact Provable.ctx_mp hΓ hBot.neg hBot hHyp hId
  | varX =>
      cases hL
  | @atom t ht =>
      let p : Var := ⟨0, .bool⟩
      let B : Formula := .imp (Formula.dneg (.atom (.var p))) (.atom (.var p))
      have hBp : SysConfig.Z.allowsFormula B := by
        have hp : SysConfig.Z.allowsFormula (.atom (.var p)) := ⟨.atom (.var p), .inr rfl⟩
        exact hp.dneg.imp hp
      have hTrue : Provable SysConfig.Z (substFormula B p (.const .trueConst)) := by
        have hSub : substFormula B p (.const .trueConst) =
            .imp (Formula.dneg (.atom (.const .trueConst))) (.atom (.const .trueConst)) := by
          simp [B]
        rw [hSub]
        exact Provable.weaken (SysConfig.allowsFormula.trueAtom _).dneg ⟨.axTrue, .axTrue, rfl⟩
      have hFalse : Provable SysConfig.Z (substFormula B p (.const .falseConst)) := by
        have hSub : substFormula B p (.const .falseConst) =
            .imp (Formula.dneg Formula.falseAtom) Formula.falseAtom := by
          simp [B, Formula.falseAtom]
        rw [hSub]
        have hF : SysConfig.Z.allowsFormula Formula.falseAtom := .falseAtom _
        have hBot : SysConfig.Z.allowsFormula .bot := .bot _
        let Γ : List Formula := [Formula.dneg Formula.falseAtom]
        have hΓ : ∀ D ∈ Γ, SysConfig.Z.allowsFormula D := by
          intro D hD; simp only [Γ, List.mem_singleton] at hD; subst hD; exact hF.dneg
        have hHyp : Provable SysConfig.Z (Formula.impMany Γ (.imp (Formula.neg Formula.falseAtom) .bot)) :=
          Provable.ctx_hyp hΓ (List.Mem.head _)
        have hAxF : Provable SysConfig.Z (Formula.impMany Γ (Formula.neg Formula.falseAtom)) :=
          Provable.ctx_const hΓ ⟨.axFalse .bot, .axFalse .bot hBot, rfl⟩
        have hBotInΓ : Provable SysConfig.Z (Formula.impMany Γ .bot) :=
          Provable.ctx_mp hΓ hF.neg hBot hHyp hAxF
        have hEfqF : Provable SysConfig.Z (Formula.impMany Γ (.imp .bot Formula.falseAtom)) :=
          Provable.ctx_const hΓ ⟨.efq Formula.falseAtom, .efq Formula.falseAtom rfl hF, rfl⟩
        exact Provable.ctx_mp hΓ hBot hF hEfqF hBotInΓ
      have hInd : Provable SysConfig.Z (indBoolFormula p B) :=
        ⟨.indBool p B, .indBool p B rfl hBp, rfl⟩
      have hAll : Provable SysConfig.Z (.all p B) :=
        Provable.mp (Provable.mp hInd hTrue) hFalse
      have hInst : Provable SysConfig.Z (substFormula B p t) :=
        Provable.all_elim p t ht hBp hAll
      have hSubT : substFormula B p t = .imp (Formula.dneg (.atom t)) (.atom t) := by
        simp [B]
      rwa [hSubT] at hInst
  | @imp B C hB hC _ ihC =>
      simp only [isLFormula, Bool.and_eq_true] at hL
      have hBa : SysConfig.Z.allowsFormula B := ⟨hB, .inr hL.1⟩
      have hCa : SysConfig.Z.allowsFormula C := ⟨hC, .inr hL.2⟩
      have hBot : SysConfig.Z.allowsFormula .bot := .bot _
      have ihC' : Provable SysConfig.Z (.imp (Formula.dneg C) C) := ihC hL.2
      let Γ0 : List Formula := [Formula.dneg (.imp B C), B]
      have hΓ0 : ∀ D ∈ Γ0, SysConfig.Z.allowsFormula D := by
        intro D hD
        simp only [Γ0, List.mem_cons, List.not_mem_nil, or_false] at hD
        rcases hD with rfl | rfl
        · exact (hBa.imp hCa).dneg
        · exact hBa
      let Γ1 : List Formula := Γ0 ++ [Formula.neg C]
      have hΓ1 : ∀ D ∈ Γ1, SysConfig.Z.allowsFormula D := by
        intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · exact hΓ0 D hD
        · simp only [List.mem_singleton] at hD; subst hD; exact hCa.neg
      let Γ2 : List Formula := Γ1 ++ [.imp B C]
      have hΓ2 : ∀ D ∈ Γ2, SysConfig.Z.allowsFormula D := by
        intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · exact hΓ1 D hD
        · simp only [List.mem_singleton] at hD; subst hD; exact hBa.imp hCa
      have hB_in_2 : Provable SysConfig.Z (Formula.impMany Γ2 B) :=
        Provable.ctx_hyp hΓ2 (by simp [Γ2, Γ1, Γ0])
      have hBC_in_2 : Provable SysConfig.Z (Formula.impMany Γ2 (.imp B C)) :=
        Provable.ctx_hyp hΓ2 (by simp [Γ2])
      have hC_in_2 : Provable SysConfig.Z (Formula.impMany Γ2 C) :=
        Provable.ctx_mp hΓ2 hBa hCa hBC_in_2 hB_in_2
      have hnC_in_2 : Provable SysConfig.Z (Formula.impMany Γ2 (.imp C .bot)) :=
        Provable.ctx_hyp hΓ2 (by simp [Γ2, Γ1, Formula.neg])
      have hBot_in_2 : Provable SysConfig.Z (Formula.impMany Γ2 .bot) :=
        Provable.ctx_mp hΓ2 hCa hBot hnC_in_2 hC_in_2
      have hnBC_in_1 : Provable SysConfig.Z (Formula.impMany Γ1 (Formula.neg (.imp B C))) := by
        simpa [Γ2, impMany_append, Formula.impMany, Formula.neg] using hBot_in_2
      have hdnBC_in_1 : Provable SysConfig.Z (Formula.impMany Γ1 (.imp (Formula.neg (.imp B C)) .bot)) :=
        Provable.ctx_hyp hΓ1 (by simp [Γ1, Γ0, Formula.dneg, Formula.neg])
      have hBot_in_1 : Provable SysConfig.Z (Formula.impMany Γ1 .bot) :=
        Provable.ctx_mp hΓ1 (hBa.imp hCa).neg hBot hdnBC_in_1 hnBC_in_1
      have hdnC_in_0 : Provable SysConfig.Z (Formula.impMany Γ0 (Formula.dneg C)) := by
        simpa [Γ1, impMany_append, Formula.impMany, Formula.dneg, Formula.neg] using hBot_in_1
      exact Provable.ctx_mp hΓ0 hCa.dneg hCa (Provable.ctx_const hΓ0 ihC') hdnC_in_0
  | @all x B hB ihB =>
      simp only [isLFormula] at hL
      have hBa : SysConfig.Z.allowsFormula B := ⟨hB, .inr hL⟩
      have hBot : SysConfig.Z.allowsFormula .bot := .bot _
      have ihB' : Provable SysConfig.Z (.imp (Formula.dneg B) B) := ihB hL
      have hElim : Provable SysConfig.Z (.imp (.all x B) B) := Provable.imp_all_elim_self x hBa
      let Γ0 : List Formula := [Formula.dneg (.all x B)]
      have hΓ0 : ∀ D ∈ Γ0, SysConfig.Z.allowsFormula D := by
        intro D hD; simp only [Γ0, List.mem_singleton] at hD; subst hD; exact (hBa.all x).dneg
      let Γ1 : List Formula := Γ0 ++ [Formula.neg B]
      have hΓ1 : ∀ D ∈ Γ1, SysConfig.Z.allowsFormula D := by
        intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · exact hΓ0 D hD
        · simp only [List.mem_singleton] at hD; subst hD; exact hBa.neg
      let Γ2 : List Formula := Γ1 ++ [.all x B]
      have hΓ2 : ∀ D ∈ Γ2, SysConfig.Z.allowsFormula D := by
        intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · exact hΓ1 D hD
        · simp only [List.mem_singleton] at hD; subst hD; exact hBa.all x
      have hAll_in_2 : Provable SysConfig.Z (Formula.impMany Γ2 (.all x B)) :=
        Provable.ctx_hyp hΓ2 (by simp [Γ2])
      have hB_in_2 : Provable SysConfig.Z (Formula.impMany Γ2 B) :=
        Provable.ctx_mp hΓ2 (hBa.all x) hBa (Provable.ctx_const hΓ2 hElim) hAll_in_2
      have hnB_in_2 : Provable SysConfig.Z (Formula.impMany Γ2 (.imp B .bot)) :=
        Provable.ctx_hyp hΓ2 (by simp [Γ2, Γ1, Formula.neg])
      have hBot_in_2 : Provable SysConfig.Z (Formula.impMany Γ2 .bot) :=
        Provable.ctx_mp hΓ2 hBa hBot hnB_in_2 hB_in_2
      have hnAll_in_1 : Provable SysConfig.Z (Formula.impMany Γ1 (Formula.neg (.all x B))) := by
        simpa [Γ2, impMany_append, Formula.impMany, Formula.neg] using hBot_in_2
      have hdnAll_in_1 : Provable SysConfig.Z (Formula.impMany Γ1 (.imp (Formula.neg (.all x B)) .bot)) :=
        Provable.ctx_hyp hΓ1 (by simp [Γ1, Γ0, Formula.dneg, Formula.neg])
      have hBot_in_1 : Provable SysConfig.Z (Formula.impMany Γ1 .bot) :=
        Provable.ctx_mp hΓ1 (hBa.all x).neg hBot hdnAll_in_1 hnAll_in_1
      have hdnB_in_0 : Provable SysConfig.Z (Formula.impMany Γ0 (Formula.dneg B)) := by
        simpa [Γ1, impMany_append, Formula.impMany, Formula.dneg, Formula.neg] using hBot_in_1
      have hB_in_0 : Provable SysConfig.Z (.imp (Formula.dneg (.all x B)) B) :=
        Provable.ctx_mp hΓ0 hBa.dneg hBa (Provable.ctx_const hΓ0 ihB') hdnB_in_0
      exact Provable.imp_all_intro x (hBa.all x).dneg (not_mem_freeVarsFormula_dneg_all x B) hB_in_0

/-! ## Section 2, Lemma 2.3 (Cases) -/

theorem lemma_2_3_cases (C A : Formula)
    (hC : FormulaWellTyped C) (hLC : isLFormula C = true) (hQFC : isQuantifierFree C = true)
    (hA : FormulaWellTyped A) :
    Provable SysConfig.ZX (.imp (.imp (Formula.neg C) A) (.imp (.imp C A) A)) := by
  have hAa : SysConfig.ZX.allowsFormula A := ⟨hA, .inl rfl⟩
  have hBot : SysConfig.ZX.allowsFormula .bot := .bot _
  induction hC with
  | bot =>
      let Γ : List Formula := [.imp (Formula.neg .bot) A, .imp .bot A]
      have hΓ : ∀ D ∈ Γ, SysConfig.ZX.allowsFormula D := by
        intro D hD
        simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hD
        rcases hD with rfl | rfl
        · exact hBot.neg.imp hAa
        · exact hBot.imp hAa
      have h1 : Provable SysConfig.ZX (Formula.impMany Γ (.imp (Formula.neg .bot) A)) :=
        Provable.ctx_hyp hΓ (by simp [Γ])
      have h2 : Provable SysConfig.ZX (Formula.impMany Γ (Formula.neg .bot)) :=
        Provable.ctx_const hΓ (Provable.id hBot)
      exact Provable.ctx_mp hΓ hBot.neg hAa h1 h2
  | varX =>
      cases hLC
  | all x _ _ =>
      cases hQFC
  | @atom t ht =>
      let p : Var := ⟨maxVarIdFormula A + 1, .bool⟩
      have hp_not_all : p ∉ allVarsFormula A :=
        not_mem_allVarsFormula_of_gt A p (by change maxVarIdFormula A < maxVarIdFormula A + 1; omega)
      have hp_not_free : p ∉ freeVarOccurrencesFormula A :=
        fun hm => hp_not_all (mem_freeVarOccurrencesFormula_of_mem_allVars hm)
      let B : Formula := .imp (.imp (Formula.neg (.atom (.var p))) A) (.imp (.imp (.atom (.var p)) A) A)
      have hBp : SysConfig.ZX.allowsFormula B := by
        have hp : SysConfig.ZX.allowsFormula (.atom (.var p)) := ⟨.atom (.var p), .inl rfl⟩
        exact (hp.neg.imp hAa).imp ((hp.imp hAa).imp hAa)
      have hSubEq : ∀ s : Term,
          FormulaBetaREq (substFormula B p s)
            (.imp (.imp (Formula.neg (.atom s)) A) (.imp (.imp (.atom s) A) A)) := by
        intro s
        have hAeq : FormulaBetaREq (substFormula A p s) A :=
          substFormula_betaREq_of_not_free A p s hp_not_free
        have h3 : substFormula B p s =
            .imp (.imp (Formula.neg (.atom s)) (substFormula A p s))
              (.imp (.imp (.atom s) (substFormula A p s)) (substFormula A p s)) := by
          simp [B]
        rw [h3]
        exact FormulaBetaREq.imp
          (FormulaBetaREq.imp (FormulaBetaREq.refl _) hAeq)
          (FormulaBetaREq.imp (FormulaBetaREq.imp (FormulaBetaREq.refl _) hAeq) hAeq)
      have hTrueRaw : Provable SysConfig.ZX
          (.imp (.imp (Formula.neg (.atom (.const .trueConst))) A)
            (.imp (.imp (.atom (.const .trueConst)) A) A)) := by
        have hT : SysConfig.ZX.allowsFormula (.atom (.const .trueConst)) := .trueAtom _
        let Γ : List Formula := [.imp (Formula.neg (.atom (.const .trueConst))) A,
          .imp (.atom (.const .trueConst)) A]
        have hΓ : ∀ D ∈ Γ, SysConfig.ZX.allowsFormula D := by
          intro D hD
          simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hD
          rcases hD with rfl | rfl
          · exact hT.neg.imp hAa
          · exact hT.imp hAa
        have hHyp : Provable SysConfig.ZX (Formula.impMany Γ (.imp (.atom (.const .trueConst)) A)) :=
          Provable.ctx_hyp hΓ (by simp [Γ])
        have hAxT : Provable SysConfig.ZX (Formula.impMany Γ (.atom (.const .trueConst))) :=
          Provable.ctx_const hΓ ⟨.axTrue, .axTrue, rfl⟩
        exact Provable.ctx_mp hΓ hT hAa hHyp hAxT
      have hTrue : Provable SysConfig.ZX (substFormula B p (.const .trueConst)) :=
        Provable.conv hTrueRaw
          (hBp.substFormula p (.const .trueConst))
          (FormulaBetaREq.symm (hSubEq (.const .trueConst)))
      have hFalseRaw : Provable SysConfig.ZX
          (.imp (.imp (Formula.neg Formula.falseAtom) A)
            (.imp (.imp Formula.falseAtom A) A)) := by
        have hF : SysConfig.ZX.allowsFormula Formula.falseAtom := .falseAtom _
        let Γ : List Formula := [.imp (Formula.neg Formula.falseAtom) A, .imp Formula.falseAtom A]
        have hΓ : ∀ D ∈ Γ, SysConfig.ZX.allowsFormula D := by
          intro D hD
          simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hD
          rcases hD with rfl | rfl
          · exact hF.neg.imp hAa
          · exact hF.imp hAa
        have hHyp : Provable SysConfig.ZX (Formula.impMany Γ (.imp (Formula.neg Formula.falseAtom) A)) :=
          Provable.ctx_hyp hΓ (by simp [Γ])
        have hAxF : Provable SysConfig.ZX (Formula.impMany Γ (Formula.neg Formula.falseAtom)) :=
          Provable.ctx_const hΓ ⟨.axFalse .bot, .axFalse .bot hBot, rfl⟩
        exact Provable.ctx_mp hΓ hF.neg hAa hHyp hAxF
      have hFalse : Provable SysConfig.ZX (substFormula B p (.const .falseConst)) :=
        Provable.conv hFalseRaw
          (hBp.substFormula p (.const .falseConst))
          (FormulaBetaREq.symm (hSubEq (.const .falseConst)))
      have hInd : Provable SysConfig.ZX (indBoolFormula p B) :=
        ⟨.indBool p B, .indBool p B rfl hBp, rfl⟩
      have hAll : Provable SysConfig.ZX (.all p B) :=
        Provable.mp (Provable.mp hInd hTrue) hFalse
      have hInst : Provable SysConfig.ZX (substFormula B p t) :=
        Provable.all_elim p t ht hBp hAll
      have hTargetAllows : SysConfig.ZX.allowsFormula
          (.imp (.imp (Formula.neg (.atom t)) A) (.imp (.imp (.atom t) A) A)) := by
        have htA : SysConfig.ZX.allowsFormula (.atom t) := ⟨.atom ht, .inl rfl⟩
        exact (htA.neg.imp hAa).imp ((htA.imp hAa).imp hAa)
      exact Provable.conv hInst hTargetAllows (hSubEq t)
  | @imp C1 C2 hC1 hC2 ih1 ih2 =>
      simp only [isLFormula, Bool.and_eq_true] at hLC
      simp only [isQuantifierFree, Bool.and_eq_true] at hQFC
      have hC1a : SysConfig.ZX.allowsFormula C1 := ⟨hC1, .inl rfl⟩
      have hC2a : SysConfig.ZX.allowsFormula C2 := ⟨hC2, .inl rfl⟩
      have hC12a : SysConfig.ZX.allowsFormula (.imp C1 C2) := hC1a.imp hC2a
      have ihC1 := ih1 hLC.1 hQFC.1
      have ihC2 := ih2 hLC.2 hQFC.2
      let Γ : List Formula := [.imp (Formula.neg (.imp C1 C2)) A, .imp (.imp C1 C2) A]
      have hΓ : ∀ D ∈ Γ, SysConfig.ZX.allowsFormula D := by
        intro D hD
        simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hD
        rcases hD with rfl | rfl
        · exact hC12a.neg.imp hAa
        · exact hC12a.imp hAa
      -- Branch 1: assume ¬C₁, derive A
      let Γ1 : List Formula := Γ ++ [Formula.neg C1]
      have hΓ1 : ∀ D ∈ Γ1, SysConfig.ZX.allowsFormula D := by
        intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · exact hΓ D hD
        · simp only [List.mem_singleton] at hD; subst hD; exact hC1a.neg
      let Γ1a : List Formula := Γ1 ++ [C1]
      have hΓ1a : ∀ D ∈ Γ1a, SysConfig.ZX.allowsFormula D := by
        intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · exact hΓ1 D hD
        · simp only [List.mem_singleton] at hD; subst hD; exact hC1a
      have hnC1_in_1a : Provable SysConfig.ZX (Formula.impMany Γ1a (.imp C1 .bot)) :=
        Provable.ctx_hyp hΓ1a (by simp [Γ1a, Γ1, Formula.neg])
      have hC1_in_1a : Provable SysConfig.ZX (Formula.impMany Γ1a C1) :=
        Provable.ctx_hyp hΓ1a (by simp [Γ1a])
      have hBot_in_1a : Provable SysConfig.ZX (Formula.impMany Γ1a .bot) :=
        Provable.ctx_mp hΓ1a hC1a hBot hnC1_in_1a hC1_in_1a
      have hEfqC2 : Provable SysConfig.ZX (Formula.impMany Γ1a (.imp .bot C2)) :=
        Provable.ctx_const hΓ1a ⟨.efq C2, .efq C2 rfl hC2a, rfl⟩
      have hC2_in_1a : Provable SysConfig.ZX (Formula.impMany Γ1a C2) :=
        Provable.ctx_mp hΓ1a hBot hC2a hEfqC2 hBot_in_1a
      have hC12_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 (.imp C1 C2)) := by
        simpa [Γ1a, impMany_append, Formula.impMany] using hC2_in_1a
      have hPosHyp_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 (.imp (.imp C1 C2) A)) :=
        Provable.ctx_hyp hΓ1 (by simp [Γ1, Γ])
      have hA_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 A) :=
        Provable.ctx_mp hΓ1 hC12a hAa hPosHyp_in_1 hC12_in_1
      have hBranch1 : Provable SysConfig.ZX (Formula.impMany Γ (.imp (Formula.neg C1) A)) := by
        simpa [Γ1, impMany_append, Formula.impMany] using hA_in_1
      -- Branch 2: assume C₁, derive A using case distinction on C₂
      let Γ2 : List Formula := Γ ++ [C1]
      have hΓ2 : ∀ D ∈ Γ2, SysConfig.ZX.allowsFormula D := by
        intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · exact hΓ D hD
        · simp only [List.mem_singleton] at hD; subst hD; exact hC1a
      -- Subbranch 2a: assume ¬C₂, derive A
      let Γ2n : List Formula := Γ2 ++ [Formula.neg C2]
      have hΓ2n : ∀ D ∈ Γ2n, SysConfig.ZX.allowsFormula D := by
        intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · exact hΓ2 D hD
        · simp only [List.mem_singleton] at hD; subst hD; exact hC2a.neg
      let Γ2na : List Formula := Γ2n ++ [.imp C1 C2]
      have hΓ2na : ∀ D ∈ Γ2na, SysConfig.ZX.allowsFormula D := by
        intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · exact hΓ2n D hD
        · simp only [List.mem_singleton] at hD; subst hD; exact hC12a
      have hC12_in_2na : Provable SysConfig.ZX (Formula.impMany Γ2na (.imp C1 C2)) :=
        Provable.ctx_hyp hΓ2na (by simp [Γ2na])
      have hC1_in_2na : Provable SysConfig.ZX (Formula.impMany Γ2na C1) :=
        Provable.ctx_hyp hΓ2na (by simp [Γ2na, Γ2n, Γ2])
      have hC2_in_2na : Provable SysConfig.ZX (Formula.impMany Γ2na C2) :=
        Provable.ctx_mp hΓ2na hC1a hC2a hC12_in_2na hC1_in_2na
      have hnC2_in_2na : Provable SysConfig.ZX (Formula.impMany Γ2na (.imp C2 .bot)) :=
        Provable.ctx_hyp hΓ2na (by simp [Γ2na, Γ2n, Formula.neg])
      have hBot_in_2na : Provable SysConfig.ZX (Formula.impMany Γ2na .bot) :=
        Provable.ctx_mp hΓ2na hC2a hBot hnC2_in_2na hC2_in_2na
      have hnC12_in_2n : Provable SysConfig.ZX (Formula.impMany Γ2n (Formula.neg (.imp C1 C2))) := by
        simpa [Γ2na, impMany_append, Formula.impMany, Formula.neg] using hBot_in_2na
      have hNegHyp_in_2n : Provable SysConfig.ZX (Formula.impMany Γ2n (.imp (Formula.neg (.imp C1 C2)) A)) :=
        Provable.ctx_hyp hΓ2n (by simp [Γ2n, Γ2, Γ])
      have hA_in_2n : Provable SysConfig.ZX (Formula.impMany Γ2n A) :=
        Provable.ctx_mp hΓ2n hC12a.neg hAa hNegHyp_in_2n hnC12_in_2n
      have hSub2n : Provable SysConfig.ZX (Formula.impMany Γ2 (.imp (Formula.neg C2) A)) := by
        simpa [Γ2n, impMany_append, Formula.impMany] using hA_in_2n
      -- Subbranch 2b: assume C₂, derive A
      let Γ2p : List Formula := Γ2 ++ [C2]
      have hΓ2p : ∀ D ∈ Γ2p, SysConfig.ZX.allowsFormula D := by
        intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · exact hΓ2 D hD
        · simp only [List.mem_singleton] at hD; subst hD; exact hC2a
      have hC2_in_2p : Provable SysConfig.ZX (Formula.impMany Γ2p C2) :=
        Provable.ctx_hyp hΓ2p (by simp [Γ2p])
      have hK_C2 : Provable SysConfig.ZX (Formula.impMany Γ2p (.imp C2 (.imp C1 C2))) :=
        Provable.ctx_const hΓ2p (Provable.imp_const hC2a hC1a)
      have hC12_in_2p : Provable SysConfig.ZX (Formula.impMany Γ2p (.imp C1 C2)) :=
        Provable.ctx_mp hΓ2p hC2a hC12a hK_C2 hC2_in_2p
      have hPosHyp_in_2p : Provable SysConfig.ZX (Formula.impMany Γ2p (.imp (.imp C1 C2) A)) :=
        Provable.ctx_hyp hΓ2p (by simp [Γ2p, Γ2, Γ])
      have hA_in_2p : Provable SysConfig.ZX (Formula.impMany Γ2p A) :=
        Provable.ctx_mp hΓ2p hC12a hAa hPosHyp_in_2p hC12_in_2p
      have hSub2p : Provable SysConfig.ZX (Formula.impMany Γ2 (.imp C2 A)) := by
        simpa [Γ2p, impMany_append, Formula.impMany] using hA_in_2p
      -- Combine subbranches 2a and 2b using ihC2
      have hStep2 : Provable SysConfig.ZX (Formula.impMany Γ2 (.imp (.imp C2 A) A)) :=
        Provable.ctx_mp hΓ2 (hC2a.neg.imp hAa) ((hC2a.imp hAa).imp hAa)
          (Provable.ctx_const hΓ2 ihC2) hSub2n
      have hA_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 A) :=
        Provable.ctx_mp hΓ2 (hC2a.imp hAa) hAa hStep2 hSub2p
      have hBranch2 : Provable SysConfig.ZX (Formula.impMany Γ (.imp C1 A)) := by
        simpa [Γ2, impMany_append, Formula.impMany] using hA_in_2
      -- Combine branches 1 and 2 using ihC1
      have hStep1 : Provable SysConfig.ZX (Formula.impMany Γ (.imp (.imp C1 A) A)) :=
        Provable.ctx_mp hΓ (hC1a.neg.imp hAa) ((hC1a.imp hAa).imp hAa)
          (Provable.ctx_const hΓ ihC1) hBranch1
      exact Provable.ctx_mp hΓ (hC1a.imp hAa) hAa hStep1 hBranch2

end BBS2002

theorem solution :
    (∀ A : BBS2002.Formula,
      BBS2002.FormulaWellTyped A →
      (BBS2002.Provable BBS2002.SysConfig.ZX A ↔
        BBS2002.Provable BBS2002.SysConfig.ZX0 (BBS2002.substBotWithFalse A))) ∧
    (∀ A : BBS2002.Formula,
      BBS2002.FormulaWellTyped A →
      BBS2002.isLFormula A = true →
      BBS2002.Provable BBS2002.SysConfig.Z (.imp (BBS2002.Formula.dneg A) A)) ∧
    (∀ C A : BBS2002.Formula,
      BBS2002.FormulaWellTyped C →
      BBS2002.isLFormula C = true →
      BBS2002.isQuantifierFree C = true →
      BBS2002.FormulaWellTyped A →
      BBS2002.Provable BBS2002.SysConfig.ZX
        (.imp (.imp (BBS2002.Formula.neg C) A) (.imp (.imp C A) A))) :=
  ⟨BBS2002.lemma_2_1, BBS2002.lemma_2_2_stability, BBS2002.lemma_2_3_cases⟩
