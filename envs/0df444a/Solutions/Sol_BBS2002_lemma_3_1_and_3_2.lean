-- Prove2me | solution 1 for BBS2002.lemma_3_1_and_3_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:17:58.28953+00:00
-- url     : https://prove2.me/submissions/afb63d6c-b19f-40cb-b447-59f79fd29daf

import Definitions.Def_BBS2002_Extraction
import Theorems.Thm_BBS2002_lemmas_2_1_to_2_3

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

theorem substTerm_var_self (r : Term) (x : Var) :
    substTerm r x (.var x) = r := by
  match r with
  | .var v =>
      rw [substTerm.eq_def]
      by_cases h : v = x
      · subst h; simp
      · have hb : (v == x) = false := beq_eq_false_iff_ne.mpr h
        simp [hb]
  | .const c =>
      rw [substTerm.eq_def]
  | .lam v body =>
      rw [substTerm.eq_def]
      by_cases h : v = x
      · subst h; simp
      · have hb : (v == x) = false := beq_eq_false_iff_ne.mpr h
        have hnot : v ∉ freeVarOccurrences (.var x) := by
          simp [freeVarOccurrences, h]
        simp [hb, hnot, substTerm_var_self body x]
  | .app t s =>
      rw [substTerm.eq_def]
      simp [substTerm_var_self t x, substTerm_var_self s x]
termination_by rawSize r
decreasing_by
  all_goals
    simp_wf
    simp [rawSize]
    try omega

theorem substFormula_var_self (A : Formula) (x : Var) :
    substFormula A x (.var x) = A := by
  match A with
  | .bot =>
      rw [substFormula.eq_def]
  | .varX =>
      rw [substFormula.eq_def]
  | .atom t =>
      rw [substFormula.eq_def]
      simp [substTerm_var_self]
  | .imp B C =>
      rw [substFormula.eq_def]
      simp [substFormula_var_self B x, substFormula_var_self C x]
  | .all v B =>
      rw [substFormula.eq_def]
      by_cases h : v = x
      · subst h; simp
      · have hb : (v == x) = false := beq_eq_false_iff_ne.mpr h
        have hnot : v ∉ freeVarOccurrences (.var x) := by
          simp [freeVarOccurrences, h]
        simp [hb, hnot, substFormula_var_self B x]
termination_by formulaSize A
decreasing_by
  all_goals
    simp_wf
    simp [formulaSize]
    try omega

theorem FormulaWellTyped.neg {A : Formula} (hA : FormulaWellTyped A) :
    FormulaWellTyped (Formula.neg A) :=
  .imp hA .bot

theorem FormulaWellTyped.dneg {A : Formula} (hA : FormulaWellTyped A) :
    FormulaWellTyped (Formula.dneg A) :=
  hA.neg.neg

theorem SysConfig.allowsFormula.bot (sys : SysConfig) : sys.allowsFormula .bot :=
  ⟨.bot, .inr rfl⟩

theorem SysConfig.allowsFormula.varX_ZX : SysConfig.ZX.allowsFormula .varX :=
  ⟨.varX, .inl rfl⟩

theorem SysConfig.allowsFormula.of_wf {A : Formula} (hA : FormulaWellTyped A) :
    SysConfig.ZX.allowsFormula A :=
  ⟨hA, .inl rfl⟩

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

theorem Provable.ctx_apply_impMany {sys : SysConfig} {Γ Δ : List Formula} {B : Formula}
    (hΓ : ∀ D ∈ Γ, sys.allowsFormula D)
    (hΔ : ∀ D ∈ Δ, sys.allowsFormula D)
    (hΔ_in_Γ : ∀ D ∈ Δ, D ∈ Γ)
    (hB : sys.allowsFormula B)
    (hf : Provable sys (Formula.impMany Γ (Formula.impMany Δ B))) :
    Provable sys (Formula.impMany Γ B) := by
  induction Δ with
  | nil => exact hf
  | cons D Δ' ih =>
      have hD : sys.allowsFormula D := hΔ D (.head _)
      have hΔ' : ∀ E ∈ Δ', sys.allowsFormula E := fun E hE => hΔ E (.tail _ hE)
      have hΔ'_in_Γ : ∀ E ∈ Δ', E ∈ Γ := fun E hE => hΔ_in_Γ E (.tail _ hE)
      have hRest : sys.allowsFormula (Formula.impMany Δ' B) := .impMany hΔ' hB
      have hHypD : Provable sys (Formula.impMany Γ D) :=
        Provable.ctx_hyp hΓ (hΔ_in_Γ D (.head _))
      exact ih hΔ' hΔ'_in_Γ (Provable.ctx_mp hΓ hD hRest hf hHypD)

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

theorem Provable.imp_all_elim {sys : SysConfig} (x : Var) (t : Term) (ht : HasType t x.ty)
    {A : Formula} (hA : sys.allowsFormula A) :
    Provable sys (.imp (.all x A) (substFormula A x t)) := by
  let u : AssumpVar := ⟨0, .all x A⟩
  have hu : sys.allowsFormula (.all x A) := hA.all x
  refine ⟨.lamAssump u (.appTerm (.assump u) t),
    .lamAssump u hu (.appTerm t ht (.assump u hu)), ?_⟩
  simp [freeAssumpVars]

theorem Provable.imp_all_elim_self {sys : SysConfig} (x : Var) {A : Formula}
    (hA : sys.allowsFormula A) :
    Provable sys (.imp (.all x A) A) := by
  have h := Provable.imp_all_elim x (.var x) (.var x) hA
  rwa [substFormula_var_self] at h

theorem Provable.all_congr {sys : SysConfig} (x : Var) {A B : Formula}
    (hA : sys.allowsFormula A) (hB : sys.allowsFormula B)
    (h : Provable sys (.imp A B)) :
    Provable sys (.imp (.all x A) (.all x B)) := by
  have hElim : Provable sys (.imp (.all x A) A) := Provable.imp_all_elim_self x hA
  let Γ : List Formula := [.all x A]
  have hΓ : ∀ D ∈ Γ, sys.allowsFormula D := by
    intro D hD; simp only [Γ, List.mem_singleton] at hD; subst hD; exact hA.all x
  have h1 : Provable sys (Formula.impMany Γ (.imp A B)) := Provable.ctx_const hΓ h
  have h2 : Provable sys (Formula.impMany Γ A) := hElim
  have h3 : Provable sys (.imp (.all x A) B) := Provable.ctx_mp hΓ hA hB h1 h2
  have hx : x ∉ freeVarsFormula (.all x A) := by
    simp [freeVarsFormula]
  exact Provable.imp_all_intro x (hA.all x) hx h3

/-! ## Properties of `substBotWithX`, `IsDefiniteFormula`, and `IsGoalFormula` -/

@[simp] theorem substBotWithX_bot : substBotWithX .bot = .varX := rfl
@[simp] theorem substBotWithX_varX : substBotWithX .varX = .varX := rfl
@[simp] theorem substBotWithX_atom (t : Term) : substBotWithX (.atom t) = .atom t := rfl
@[simp] theorem substBotWithX_imp (B C : Formula) :
    substBotWithX (.imp B C) = .imp (substBotWithX B) (substBotWithX C) := rfl
@[simp] theorem substBotWithX_all (x : Var) (B : Formula) :
    substBotWithX (.all x B) = .all x (substBotWithX B) := rfl

@[simp]
theorem freeVarsFormula_substBotWithX (A : Formula) :
    freeVarsFormula (substBotWithX A) = freeVarsFormula A := by
  induction A with
  | bot | varX | atom _ => rfl
  | imp B C ihB ihC => simp [freeVarsFormula, ihB, ihC]
  | all x B ih => simp [freeVarsFormula, ih]

theorem FormulaWellTyped.substBotWithX {A : Formula} (hA : FormulaWellTyped A) :
    FormulaWellTyped (BBS2002.substBotWithX A) := by
  induction hA with
  | bot => exact .varX
  | varX => exact .varX
  | atom ht => exact .atom ht
  | imp _ _ ih1 ih2 => exact .imp ih1 ih2
  | all x _ ih => exact .all x ih

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

theorem not_mem_freeVarsFormula_imp_neg_all_varX (x : Var) (D : Formula) :
    x ∉ freeVarsFormula (.imp (Formula.neg (.all x D)) .varX) := by
  simp [Formula.neg, freeVarsFormula]

/-! ## Section 3, Lemma 3.1 (Equations (3)–(6)) -/

theorem lemma_3_1_aux (A : Formula) :
    (IsDefiniteFormula A →
      (isRelevant A = true →
        Provable SysConfig.ZX (.imp (.imp (Formula.neg A) .varX) (substBotWithX A))) ∧
      Provable SysConfig.ZX (.imp A (substBotWithX A))) ∧
    (IsGoalFormula A →
      (isIrrelevant A = true →
        Provable SysConfig.ZX (.imp (substBotWithX A) A)) ∧
      Provable SysConfig.ZX (.imp (substBotWithX A) (.imp (.imp A .varX) .varX))) := by
  have hBot : SysConfig.ZX.allowsFormula .bot := .bot _
  have hX : SysConfig.ZX.allowsFormula .varX := .varX_ZX
  induction A with
  | bot =>
      refine ⟨fun _ => ⟨fun _ => ?_, ?_⟩, fun _ => ⟨fun hIrr => ?_, ?_⟩⟩
      · -- (3) for ⊥: (¬⊥ → X) → X
        let Γ : List Formula := [.imp (Formula.neg .bot) .varX]
        have hΓ : ∀ E ∈ Γ, SysConfig.ZX.allowsFormula E := by
          intro E hE; simp only [Γ, List.mem_singleton] at hE; subst hE; exact hBot.neg.imp hX
        have h1 : Provable SysConfig.ZX (Formula.impMany Γ (.imp (Formula.neg .bot) .varX)) :=
          Provable.ctx_hyp hΓ (.head _)
        have h2 : Provable SysConfig.ZX (Formula.impMany Γ (Formula.neg .bot)) :=
          Provable.ctx_const hΓ (Provable.id hBot)
        exact Provable.ctx_mp hΓ hBot.neg hX h1 h2
      · -- (4) for ⊥: ⊥ → X
        exact ⟨.efq .varX, .efq .varX rfl hX, rfl⟩
      · -- (5) for ⊥: impossible since isIrrelevant ⊥ = false
        cases hIrr
      · -- (6) for ⊥: X → (⊥ → X) → X
        exact Provable.imp_const hX (hBot.imp hX)
  | varX =>
      refine ⟨fun hD => ?_, fun hG => ?_⟩
      · cases hD with | atom hAt _ => cases hAt
      · cases hG with | atom hAt _ => cases hAt
  | atom t =>
      refine ⟨fun hD => ?_, fun hG => ?_⟩
      · have hwf : FormulaWellTyped (.atom t) := (IsDefinite_IsGoal_wf_and_L (.atom t)).1 hD |>.1
        have hAt : SysConfig.ZX.allowsFormula (.atom t) := .of_wf hwf
        refine ⟨fun hRel => ?_, Provable.id hAt⟩
        cases hRel
      · have hwf : FormulaWellTyped (.atom t) := (IsDefinite_IsGoal_wf_and_L (.atom t)).2 hG |>.1
        have hAt : SysConfig.ZX.allowsFormula (.atom t) := .of_wf hwf
        refine ⟨fun _ => Provable.id hAt, ?_⟩
        let Γ : List Formula := [.atom t, .imp (.atom t) .varX]
        have hΓ : ∀ E ∈ Γ, SysConfig.ZX.allowsFormula E := by
          intro E hE
          simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hE
          rcases hE with rfl | rfl
          · exact hAt
          · exact hAt.imp hX
        have h1 : Provable SysConfig.ZX (Formula.impMany Γ (.imp (.atom t) .varX)) :=
          Provable.ctx_hyp hΓ (by simp [Γ])
        have h2 : Provable SysConfig.ZX (Formula.impMany Γ (.atom t)) :=
          Provable.ctx_hyp hΓ (by simp [Γ])
        exact Provable.ctx_mp hΓ hAt hX h1 h2
  | imp B C ihB ihC =>
      refine ⟨fun hD => ?_, fun hG => ?_⟩
      · -- Definite formula G → D (where G = B, D = C)
        cases hD with
        | atom hAt _ => cases hAt
        | imp hG_B hD_C hCrit =>
            have hwfB := (IsDefinite_IsGoal_wf_and_L B).2 hG_B
            have hwfC := (IsDefinite_IsGoal_wf_and_L C).1 hD_C
            have hBa : SysConfig.ZX.allowsFormula B := .of_wf hwfB.1
            have hBXa : SysConfig.ZX.allowsFormula (substBotWithX B) := .of_wf hwfB.1.substBotWithX
            have hCa : SysConfig.ZX.allowsFormula C := .of_wf hwfC.1
            have hCXa : SysConfig.ZX.allowsFormula (substBotWithX C) := .of_wf hwfC.1.substBotWithX
            have ihG := ihB.2 hG_B
            have ihD := ihC.1 hD_C
            have hEq3_when_rel : isRelevant C = true →
                Provable SysConfig.ZX
                  (.imp (.imp (Formula.neg (.imp B C)) .varX)
                    (.imp (substBotWithX B) (substBotWithX C))) := by
              intro hRelC
              have ihD3 := ihD.1 hRelC
              have ihG6 := ihG.2
              let Γ0 : List Formula := [.imp (Formula.neg (.imp B C)) .varX, substBotWithX B]
              have hΓ0 : ∀ E ∈ Γ0, SysConfig.ZX.allowsFormula E := by
                intro E hE
                simp only [Γ0, List.mem_cons, List.not_mem_nil, or_false] at hE
                rcases hE with rfl | rfl
                · exact (hBa.imp hCa).neg.imp hX
                · exact hBXa
              let Γ1 : List Formula := Γ0 ++ [Formula.neg C]
              have hΓ1 : ∀ E ∈ Γ1, SysConfig.ZX.allowsFormula E := by
                intro E hE
                rcases List.mem_append.mp hE with hE | hE
                · exact hΓ0 E hE
                · simp only [List.mem_singleton] at hE; subst hE; exact hCa.neg
              let Γ2 : List Formula := Γ1 ++ [B]
              have hΓ2 : ∀ E ∈ Γ2, SysConfig.ZX.allowsFormula E := by
                intro E hE
                rcases List.mem_append.mp hE with hE | hE
                · exact hΓ1 E hE
                · simp only [List.mem_singleton] at hE; subst hE; exact hBa
              let Γ3 : List Formula := Γ2 ++ [.imp B C]
              have hΓ3 : ∀ E ∈ Γ3, SysConfig.ZX.allowsFormula E := by
                intro E hE
                rcases List.mem_append.mp hE with hE | hE
                · exact hΓ2 E hE
                · simp only [List.mem_singleton] at hE; subst hE; exact hBa.imp hCa
              have hBC_in_3 : Provable SysConfig.ZX (Formula.impMany Γ3 (.imp B C)) :=
                Provable.ctx_hyp hΓ3 (by simp [Γ3])
              have hB_in_3 : Provable SysConfig.ZX (Formula.impMany Γ3 B) :=
                Provable.ctx_hyp hΓ3 (by simp [Γ3, Γ2])
              have hC_in_3 : Provable SysConfig.ZX (Formula.impMany Γ3 C) :=
                Provable.ctx_mp hΓ3 hBa hCa hBC_in_3 hB_in_3
              have hnC_in_3 : Provable SysConfig.ZX (Formula.impMany Γ3 (.imp C .bot)) :=
                Provable.ctx_hyp hΓ3 (by simp [Γ3, Γ2, Γ1, Formula.neg])
              have hBot_in_3 : Provable SysConfig.ZX (Formula.impMany Γ3 .bot) :=
                Provable.ctx_mp hΓ3 hCa hBot hnC_in_3 hC_in_3
              have hnBC_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 (Formula.neg (.imp B C))) := by
                simpa [Γ3, impMany_append, Formula.impMany, Formula.neg] using hBot_in_3
              have hHyp_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 (.imp (Formula.neg (.imp B C)) .varX)) :=
                Provable.ctx_hyp hΓ2 (by simp [Γ2, Γ1, Γ0])
              have hX_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 .varX) :=
                Provable.ctx_mp hΓ2 (hBa.imp hCa).neg hX hHyp_in_2 hnBC_in_2
              have hBX_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 (.imp B .varX)) := by
                simpa [Γ2, impMany_append, Formula.impMany] using hX_in_2
              have hSubB_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 (substBotWithX B)) :=
                Provable.ctx_hyp hΓ1 (by simp [Γ1, Γ0])
              have hStepG6 : Provable SysConfig.ZX (Formula.impMany Γ1 (.imp (.imp B .varX) .varX)) :=
                Provable.ctx_mp hΓ1 hBXa ((hBa.imp hX).imp hX) (Provable.ctx_const hΓ1 ihG6) hSubB_in_1
              have hX_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 .varX) :=
                Provable.ctx_mp hΓ1 (hBa.imp hX) hX hStepG6 hBX_in_1
              have hnCX_in_0 : Provable SysConfig.ZX (Formula.impMany Γ0 (.imp (Formula.neg C) .varX)) := by
                simpa [Γ1, impMany_append, Formula.impMany] using hX_in_1
              exact Provable.ctx_mp hΓ0 (hCa.neg.imp hX) hCXa (Provable.ctx_const hΓ0 ihD3) hnCX_in_0
            refine ⟨fun hRel => hEq3_when_rel hRel, ?_⟩
            -- (4) for G → D: (B → C) → B^X → C^X
            cases hRelC : isRelevant C with
            | false =>
                have hIrrC : isIrrelevant C = true := by simp [isIrrelevant, hRelC]
                have hIrrB : isIrrelevant B = true := hCrit hIrrC
                have ihG5 := ihG.1 hIrrB
                have ihD4 := ihD.2
                let Γ : List Formula := [.imp B C, substBotWithX B]
                have hΓ : ∀ E ∈ Γ, SysConfig.ZX.allowsFormula E := by
                  intro E hE
                  simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hE
                  rcases hE with rfl | rfl
                  · exact hBa.imp hCa
                  · exact hBXa
                have hSubB : Provable SysConfig.ZX (Formula.impMany Γ (substBotWithX B)) :=
                  Provable.ctx_hyp hΓ (by simp [Γ])
                have hB_in_Γ : Provable SysConfig.ZX (Formula.impMany Γ B) :=
                  Provable.ctx_mp hΓ hBXa hBa (Provable.ctx_const hΓ ihG5) hSubB
                have hBC_in_Γ : Provable SysConfig.ZX (Formula.impMany Γ (.imp B C)) :=
                  Provable.ctx_hyp hΓ (by simp [Γ])
                have hC_in_Γ : Provable SysConfig.ZX (Formula.impMany Γ C) :=
                  Provable.ctx_mp hΓ hBa hCa hBC_in_Γ hB_in_Γ
                exact Provable.ctx_mp hΓ hCa hCXa (Provable.ctx_const hΓ ihD4) hC_in_Γ
            | true =>
                have ihD3 := ihD.1 hRelC
                have ihG6 := ihG.2
                let Γ0 : List Formula := [.imp B C, substBotWithX B]
                have hΓ0 : ∀ E ∈ Γ0, SysConfig.ZX.allowsFormula E := by
                  intro E hE
                  simp only [Γ0, List.mem_cons, List.not_mem_nil, or_false] at hE
                  rcases hE with rfl | rfl
                  · exact hBa.imp hCa
                  · exact hBXa
                let Γ1 : List Formula := Γ0 ++ [Formula.neg C]
                have hΓ1 : ∀ E ∈ Γ1, SysConfig.ZX.allowsFormula E := by
                  intro E hE
                  rcases List.mem_append.mp hE with hE | hE
                  · exact hΓ0 E hE
                  · simp only [List.mem_singleton] at hE; subst hE; exact hCa.neg
                let Γ2 : List Formula := Γ1 ++ [B]
                have hΓ2 : ∀ E ∈ Γ2, SysConfig.ZX.allowsFormula E := by
                  intro E hE
                  rcases List.mem_append.mp hE with hE | hE
                  · exact hΓ1 E hE
                  · simp only [List.mem_singleton] at hE; subst hE; exact hBa
                have hBC_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 (.imp B C)) :=
                  Provable.ctx_hyp hΓ2 (by simp [Γ2, Γ1, Γ0])
                have hB_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 B) :=
                  Provable.ctx_hyp hΓ2 (by simp [Γ2])
                have hC_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 C) :=
                  Provable.ctx_mp hΓ2 hBa hCa hBC_in_2 hB_in_2
                have hnC_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 (.imp C .bot)) :=
                  Provable.ctx_hyp hΓ2 (by simp [Γ2, Γ1, Formula.neg])
                have hBot_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 .bot) :=
                  Provable.ctx_mp hΓ2 hCa hBot hnC_in_2 hC_in_2
                have hEfqX : Provable SysConfig.ZX (Formula.impMany Γ2 (.imp .bot .varX)) :=
                  Provable.ctx_const hΓ2 ⟨.efq .varX, .efq .varX rfl hX, rfl⟩
                have hX_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 .varX) :=
                  Provable.ctx_mp hΓ2 hBot hX hEfqX hBot_in_2
                have hBX_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 (.imp B .varX)) := by
                  simpa [Γ2, impMany_append, Formula.impMany] using hX_in_2
                have hSubB_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 (substBotWithX B)) :=
                  Provable.ctx_hyp hΓ1 (by simp [Γ1, Γ0])
                have hStepG6 : Provable SysConfig.ZX (Formula.impMany Γ1 (.imp (.imp B .varX) .varX)) :=
                  Provable.ctx_mp hΓ1 hBXa ((hBa.imp hX).imp hX) (Provable.ctx_const hΓ1 ihG6) hSubB_in_1
                have hX_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 .varX) :=
                  Provable.ctx_mp hΓ1 (hBa.imp hX) hX hStepG6 hBX_in_1
                have hnCX_in_0 : Provable SysConfig.ZX (Formula.impMany Γ0 (.imp (Formula.neg C) .varX)) := by
                  simpa [Γ1, impMany_append, Formula.impMany] using hX_in_1
                exact Provable.ctx_mp hΓ0 (hCa.neg.imp hX) hCXa (Provable.ctx_const hΓ0 ihD3) hnCX_in_0
      · -- Goal formula D → G (where D = B, G = C)
        cases hG with
        | atom hAt _ => cases hAt
        | imp hD_B hG_C hQFB =>
            have hwfB := (IsDefinite_IsGoal_wf_and_L B).1 hD_B
            have hwfC := (IsDefinite_IsGoal_wf_and_L C).2 hG_C
            have hBa : SysConfig.ZX.allowsFormula B := .of_wf hwfB.1
            have hBXa : SysConfig.ZX.allowsFormula (substBotWithX B) := .of_wf hwfB.1.substBotWithX
            have hCa : SysConfig.ZX.allowsFormula C := .of_wf hwfC.1
            have hCXa : SysConfig.ZX.allowsFormula (substBotWithX C) := .of_wf hwfC.1.substBotWithX
            have ihD := ihB.1 hD_B
            have ihG := ihC.2 hG_C
            refine ⟨fun hIrr => ?_, ?_⟩
            · -- (5) for D → G: (B^X → C^X) → B → C when isIrrelevant (B → C) = true
              have hIrrC : isIrrelevant C = true := hIrr
              have ihG5 := ihG.1 hIrrC
              have ihD4 := ihD.2
              let Γ : List Formula := [.imp (substBotWithX B) (substBotWithX C), B]
              have hΓ : ∀ E ∈ Γ, SysConfig.ZX.allowsFormula E := by
                intro E hE
                simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hE
                rcases hE with rfl | rfl
                · exact hBXa.imp hCXa
                · exact hBa
              have hB_in_Γ : Provable SysConfig.ZX (Formula.impMany Γ B) :=
                Provable.ctx_hyp hΓ (by simp [Γ])
              have hBX_in_Γ : Provable SysConfig.ZX (Formula.impMany Γ (substBotWithX B)) :=
                Provable.ctx_mp hΓ hBa hBXa (Provable.ctx_const hΓ ihD4) hB_in_Γ
              have hImp_in_Γ : Provable SysConfig.ZX (Formula.impMany Γ (.imp (substBotWithX B) (substBotWithX C))) :=
                Provable.ctx_hyp hΓ (by simp [Γ])
              have hCX_in_Γ : Provable SysConfig.ZX (Formula.impMany Γ (substBotWithX C)) :=
                Provable.ctx_mp hΓ hBXa hCXa hImp_in_Γ hBX_in_Γ
              exact Provable.ctx_mp hΓ hCXa hCa (Provable.ctx_const hΓ ihG5) hCX_in_Γ
            · -- (6) for D → G: (B^X → C^X) → ((B → C) → X) → X
              have ihD4 := ihD.2
              have ihG6 := ihG.2
              let Γ0 : List Formula := [.imp (substBotWithX B) (substBotWithX C), .imp (.imp B C) .varX]
              have hΓ0 : ∀ E ∈ Γ0, SysConfig.ZX.allowsFormula E := by
                intro E hE
                simp only [Γ0, List.mem_cons, List.not_mem_nil, or_false] at hE
                rcases hE with rfl | rfl
                · exact hBXa.imp hCXa
                · exact (hBa.imp hCa).imp hX
              -- Helper 1: Γ0 ⊢ ¬B → X
              have hnB_to_X : Provable SysConfig.ZX (Formula.impMany Γ0 (.imp (Formula.neg B) .varX)) := by
                let Γ1 : List Formula := Γ0 ++ [Formula.neg B]
                have hΓ1 : ∀ E ∈ Γ1, SysConfig.ZX.allowsFormula E := by
                  intro E hE
                  rcases List.mem_append.mp hE with hE | hE
                  · exact hΓ0 E hE
                  · simp only [List.mem_singleton] at hE; subst hE; exact hBa.neg
                let Γ1a : List Formula := Γ1 ++ [B]
                have hΓ1a : ∀ E ∈ Γ1a, SysConfig.ZX.allowsFormula E := by
                  intro E hE
                  rcases List.mem_append.mp hE with hE | hE
                  · exact hΓ1 E hE
                  · simp only [List.mem_singleton] at hE; subst hE; exact hBa
                have hnB_in_1a : Provable SysConfig.ZX (Formula.impMany Γ1a (.imp B .bot)) :=
                  Provable.ctx_hyp hΓ1a (by simp [Γ1a, Γ1, Formula.neg])
                have hB_in_1a : Provable SysConfig.ZX (Formula.impMany Γ1a B) :=
                  Provable.ctx_hyp hΓ1a (by simp [Γ1a])
                have hBot_in_1a : Provable SysConfig.ZX (Formula.impMany Γ1a .bot) :=
                  Provable.ctx_mp hΓ1a hBa hBot hnB_in_1a hB_in_1a
                have hEfqC : Provable SysConfig.ZX (Formula.impMany Γ1a (.imp .bot C)) :=
                  Provable.ctx_const hΓ1a ⟨.efq C, .efq C rfl hCa, rfl⟩
                have hC_in_1a : Provable SysConfig.ZX (Formula.impMany Γ1a C) :=
                  Provable.ctx_mp hΓ1a hBot hCa hEfqC hBot_in_1a
                have hBC_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 (.imp B C)) := by
                  simpa [Γ1a, impMany_append, Formula.impMany] using hC_in_1a
                have hHyp_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 (.imp (.imp B C) .varX)) :=
                  Provable.ctx_hyp hΓ1 (by simp [Γ1, Γ0])
                have hX_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 .varX) :=
                  Provable.ctx_mp hΓ1 (hBa.imp hCa) hX hHyp_in_1 hBC_in_1
                simpa [Γ1, impMany_append, Formula.impMany] using hX_in_1
              -- Helper 2: Γ0 ⊢ C → X
              have hC_to_X : Provable SysConfig.ZX (Formula.impMany Γ0 (.imp C .varX)) := by
                let Γ2 : List Formula := Γ0 ++ [C]
                have hΓ2 : ∀ E ∈ Γ2, SysConfig.ZX.allowsFormula E := by
                  intro E hE
                  rcases List.mem_append.mp hE with hE | hE
                  · exact hΓ0 E hE
                  · simp only [List.mem_singleton] at hE; subst hE; exact hCa
                have hC_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 C) :=
                  Provable.ctx_hyp hΓ2 (by simp [Γ2])
                have hKC : Provable SysConfig.ZX (Formula.impMany Γ2 (.imp C (.imp B C))) :=
                  Provable.ctx_const hΓ2 (Provable.imp_const hCa hBa)
                have hBC_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 (.imp B C)) :=
                  Provable.ctx_mp hΓ2 hCa (hBa.imp hCa) hKC hC_in_2
                have hHyp_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 (.imp (.imp B C) .varX)) :=
                  Provable.ctx_hyp hΓ2 (by simp [Γ2, Γ0])
                have hX_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 .varX) :=
                  Provable.ctx_mp hΓ2 (hBa.imp hCa) hX hHyp_in_2 hBC_in_2
                simpa [Γ2, impMany_append, Formula.impMany] using hX_in_2
              -- Helper 3: Γ0 ⊢ B^X → X
              have hBX_to_X : Provable SysConfig.ZX (Formula.impMany Γ0 (.imp (substBotWithX B) .varX)) := by
                let Γ3 : List Formula := Γ0 ++ [substBotWithX B]
                have hΓ3 : ∀ E ∈ Γ3, SysConfig.ZX.allowsFormula E := by
                  intro E hE
                  rcases List.mem_append.mp hE with hE | hE
                  · exact hΓ0 E hE
                  · simp only [List.mem_singleton] at hE; subst hE; exact hBXa
                have hBX_in_3 : Provable SysConfig.ZX (Formula.impMany Γ3 (substBotWithX B)) :=
                  Provable.ctx_hyp hΓ3 (by simp [Γ3])
                have hImp_in_3 : Provable SysConfig.ZX (Formula.impMany Γ3 (.imp (substBotWithX B) (substBotWithX C))) :=
                  Provable.ctx_hyp hΓ3 (by simp [Γ3, Γ0])
                have hCX_in_3 : Provable SysConfig.ZX (Formula.impMany Γ3 (substBotWithX C)) :=
                  Provable.ctx_mp hΓ3 hBXa hCXa hImp_in_3 hBX_in_3
                have hStepG6 : Provable SysConfig.ZX (Formula.impMany Γ3 (.imp (.imp C .varX) .varX)) :=
                  Provable.ctx_mp hΓ3 hCXa ((hCa.imp hX).imp hX) (Provable.ctx_const hΓ3 ihG6) hCX_in_3
                have hCX_hyp_3 : Provable SysConfig.ZX (Formula.impMany Γ3 (.imp C .varX)) := by
                  simpa [Γ3, impMany_append, Formula.impMany] using
                    Provable.ctx_mp hΓ0 (hCa.imp hX) (hBXa.imp (hCa.imp hX))
                      (Provable.ctx_const hΓ0 (Provable.imp_const (hCa.imp hX) hBXa)) hC_to_X
                have hX_in_3 : Provable SysConfig.ZX (Formula.impMany Γ3 .varX) :=
                  Provable.ctx_mp hΓ3 (hCa.imp hX) hX hStepG6 hCX_hyp_3
                simpa [Γ3, impMany_append, Formula.impMany] using hX_in_3
              cases hRelB : isRelevant B with
              | true =>
                  have ihD3 := ihD.1 hRelB
                  have hBX_in_0 : Provable SysConfig.ZX (Formula.impMany Γ0 (substBotWithX B)) :=
                    Provable.ctx_mp hΓ0 (hBa.neg.imp hX) hBXa (Provable.ctx_const hΓ0 ihD3) hnB_to_X
                  exact Provable.ctx_mp hΓ0 hBXa hX hBX_to_X hBX_in_0
              | false =>
                  have hIrrB : isIrrelevant B = true := by simp [isIrrelevant, hRelB]
                  have hQFB' : isQuantifierFree B = true := hQFB hIrrB
                  have hCases : Provable SysConfig.ZX
                      (.imp (.imp (Formula.neg B) .varX) (.imp (.imp B .varX) .varX)) :=
                    lemmas_2_1_to_2_3.2.2 B .varX hwfB.1 hwfB.2 hQFB' .varX
                  -- Derive Γ0 ⊢ B → X from ihD4 : B → B^X and hBX_to_X : Γ0 ⊢ B^X → X
                  let Γ4 : List Formula := Γ0 ++ [B]
                  have hΓ4 : ∀ E ∈ Γ4, SysConfig.ZX.allowsFormula E := by
                    intro E hE
                    rcases List.mem_append.mp hE with hE | hE
                    · exact hΓ0 E hE
                    · simp only [List.mem_singleton] at hE; subst hE; exact hBa
                  have hB_in_4 : Provable SysConfig.ZX (Formula.impMany Γ4 B) :=
                    Provable.ctx_hyp hΓ4 (by simp [Γ4])
                  have hBX_in_4 : Provable SysConfig.ZX (Formula.impMany Γ4 (substBotWithX B)) :=
                    Provable.ctx_mp hΓ4 hBa hBXa (Provable.ctx_const hΓ4 ihD4) hB_in_4
                  have hBX_to_X_4 : Provable SysConfig.ZX (Formula.impMany Γ4 (.imp (substBotWithX B) .varX)) := by
                    simpa [Γ4, impMany_append, Formula.impMany] using
                      Provable.ctx_mp hΓ0 (hBXa.imp hX) (hBa.imp (hBXa.imp hX))
                        (Provable.ctx_const hΓ0 (Provable.imp_const (hBXa.imp hX) hBa)) hBX_to_X
                  have hX_in_4 : Provable SysConfig.ZX (Formula.impMany Γ4 .varX) :=
                    Provable.ctx_mp hΓ4 hBXa hX hBX_to_X_4 hBX_in_4
                  have hB_to_X : Provable SysConfig.ZX (Formula.impMany Γ0 (.imp B .varX)) := by
                    simpa [Γ4, impMany_append, Formula.impMany] using hX_in_4
                  have hStepCases : Provable SysConfig.ZX (Formula.impMany Γ0 (.imp (.imp B .varX) .varX)) :=
                    Provable.ctx_mp hΓ0 (hBa.neg.imp hX) ((hBa.imp hX).imp hX)
                      (Provable.ctx_const hΓ0 hCases) hnB_to_X
                  exact Provable.ctx_mp hΓ0 (hBa.imp hX) hX hStepCases hB_to_X
  | all x B ihB =>
      refine ⟨fun hD => ?_, fun hG => ?_⟩
      · -- Definite formula ∀x D
        cases hD with
        | atom hAt _ => cases hAt
        | all _ hD_B =>
            have hwfB := (IsDefinite_IsGoal_wf_and_L B).1 hD_B
            have hBa : SysConfig.ZX.allowsFormula B := .of_wf hwfB.1
            have hBXa : SysConfig.ZX.allowsFormula (substBotWithX B) := .of_wf hwfB.1.substBotWithX
            have ihD := ihB.1 hD_B
            refine ⟨fun hRel => ?_, Provable.all_congr x hBa hBXa ihD.2⟩
            -- (3) for ∀x B: (¬∀x B → X) → ∀x B^X
            have ihD3 := ihD.1 hRel
            have hElim : Provable SysConfig.ZX (.imp (.all x B) B) := Provable.imp_all_elim_self x hBa
            let Γ0 : List Formula := [.imp (Formula.neg (.all x B)) .varX]
            have hΓ0 : ∀ E ∈ Γ0, SysConfig.ZX.allowsFormula E := by
              intro E hE; simp only [Γ0, List.mem_singleton] at hE; subst hE; exact (hBa.all x).neg.imp hX
            let Γ1 : List Formula := Γ0 ++ [Formula.neg B]
            have hΓ1 : ∀ E ∈ Γ1, SysConfig.ZX.allowsFormula E := by
              intro E hE
              rcases List.mem_append.mp hE with hE | hE
              · exact hΓ0 E hE
              · simp only [List.mem_singleton] at hE; subst hE; exact hBa.neg
            let Γ2 : List Formula := Γ1 ++ [.all x B]
            have hΓ2 : ∀ E ∈ Γ2, SysConfig.ZX.allowsFormula E := by
              intro E hE
              rcases List.mem_append.mp hE with hE | hE
              · exact hΓ1 E hE
              · simp only [List.mem_singleton] at hE; subst hE; exact hBa.all x
            have hAll_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 (.all x B)) :=
              Provable.ctx_hyp hΓ2 (by simp [Γ2])
            have hB_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 B) :=
              Provable.ctx_mp hΓ2 (hBa.all x) hBa (Provable.ctx_const hΓ2 hElim) hAll_in_2
            have hnB_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 (.imp B .bot)) :=
              Provable.ctx_hyp hΓ2 (by simp [Γ2, Γ1, Formula.neg])
            have hBot_in_2 : Provable SysConfig.ZX (Formula.impMany Γ2 .bot) :=
              Provable.ctx_mp hΓ2 hBa hBot hnB_in_2 hB_in_2
            have hnAll_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 (Formula.neg (.all x B))) := by
              simpa [Γ2, impMany_append, Formula.impMany, Formula.neg] using hBot_in_2
            have hHyp_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 (.imp (Formula.neg (.all x B)) .varX)) :=
              Provable.ctx_hyp hΓ1 (by simp [Γ1, Γ0])
            have hX_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 .varX) :=
              Provable.ctx_mp hΓ1 (hBa.all x).neg hX hHyp_in_1 hnAll_in_1
            have hnBX_in_0 : Provable SysConfig.ZX (Formula.impMany Γ0 (.imp (Formula.neg B) .varX)) := by
              simpa [Γ1, impMany_append, Formula.impMany] using hX_in_1
            have hBX_in_0 : Provable SysConfig.ZX (.imp (.imp (Formula.neg (.all x B)) .varX) (substBotWithX B)) :=
              Provable.ctx_mp hΓ0 (hBa.neg.imp hX) hBXa (Provable.ctx_const hΓ0 ihD3) hnBX_in_0
            exact Provable.imp_all_intro x ((hBa.all x).neg.imp hX)
              (not_mem_freeVarsFormula_imp_neg_all_varX x B) hBX_in_0
      · -- Goal formula ∀x G
        cases hG with
        | atom hAt _ => cases hAt
        | all _ hG_B hIrrB =>
            have hwfB := (IsDefinite_IsGoal_wf_and_L B).2 hG_B
            have hBa : SysConfig.ZX.allowsFormula B := .of_wf hwfB.1
            have hBXa : SysConfig.ZX.allowsFormula (substBotWithX B) := .of_wf hwfB.1.substBotWithX
            have ihG5 := (ihB.2 hG_B).1 hIrrB
            have hAll5 : Provable SysConfig.ZX (.imp (.all x (substBotWithX B)) (.all x B)) :=
              Provable.all_congr x hBXa hBa ihG5
            refine ⟨fun _ => hAll5, ?_⟩
            let Γ : List Formula := [.all x (substBotWithX B), .imp (.all x B) .varX]
            have hΓ : ∀ E ∈ Γ, SysConfig.ZX.allowsFormula E := by
              intro E hE
              simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hE
              rcases hE with rfl | rfl
              · exact hBXa.all x
              · exact (hBa.all x).imp hX
            have hAllX_in_Γ : Provable SysConfig.ZX (Formula.impMany Γ (.all x (substBotWithX B))) :=
              Provable.ctx_hyp hΓ (by simp [Γ])
            have hAll_in_Γ : Provable SysConfig.ZX (Formula.impMany Γ (.all x B)) :=
              Provable.ctx_mp hΓ (hBXa.all x) (hBa.all x) (Provable.ctx_const hΓ hAll5) hAllX_in_Γ
            have hImp_in_Γ : Provable SysConfig.ZX (Formula.impMany Γ (.imp (.all x B) .varX)) :=
              Provable.ctx_hyp hΓ (by simp [Γ])
            exact Provable.ctx_mp hΓ (hBa.all x) hX hImp_in_Γ hAll_in_Γ

/-! ## Section 3, Lemma 3.2 -/

theorem lemma_3_2 (Gs : List Formula) (hGs : ∀ G ∈ Gs, IsGoalFormula G) :
    Provable SysConfig.ZX
      (.imp
        (Formula.impMany Gs .varX)
        (Formula.impMany (Gs.map substBotWithX) .varX)) := by
  have hX : SysConfig.ZX.allowsFormula .varX := .varX_ZX
  induction Gs with
  | nil =>
      exact Provable.id hX
  | cons G Gs' ih =>
      have hG : IsGoalFormula G := hGs G (.head _)
      have hGs' : ∀ E ∈ Gs', IsGoalFormula E := fun E hE => hGs E (.tail _ hE)
      have hwfG := (IsDefinite_IsGoal_wf_and_L G).2 hG
      have hGa : SysConfig.ZX.allowsFormula G := .of_wf hwfG.1
      have hGXa : SysConfig.ZX.allowsFormula (substBotWithX G) := .of_wf hwfG.1.substBotWithX
      have hGs'a : ∀ E ∈ Gs', SysConfig.ZX.allowsFormula E := by
        intro E hE
        exact .of_wf ((IsDefinite_IsGoal_wf_and_L E).2 (hGs' E hE)).1
      have hGs'Xa : ∀ E ∈ Gs'.map substBotWithX, SysConfig.ZX.allowsFormula E := by
        intro E hE
        rcases List.mem_map.mp hE with ⟨F, hF, rfl⟩
        exact .of_wf ((IsDefinite_IsGoal_wf_and_L F).2 (hGs' F hF)).1.substBotWithX
      have hRest : SysConfig.ZX.allowsFormula (Formula.impMany Gs' .varX) := .impMany hGs'a hX
      have hRestX : SysConfig.ZX.allowsFormula (Formula.impMany (Gs'.map substBotWithX) .varX) :=
        .impMany hGs'Xa hX
      have ih' := ih hGs'
      have hG6 := ((lemma_3_1_aux G).2 hG).2
      let Γ0 : List Formula :=
        [.imp G (Formula.impMany Gs' .varX), substBotWithX G] ++ Gs'.map substBotWithX
      have hΓ0 : ∀ E ∈ Γ0, SysConfig.ZX.allowsFormula E := by
        intro E hE
        rcases List.mem_append.mp hE with hE | hE
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
          rcases hE with rfl | rfl
          · exact hGa.imp hRest
          · exact hGXa
        · exact hGs'Xa E hE
      let Γ1 : List Formula := Γ0 ++ [G]
      have hΓ1 : ∀ E ∈ Γ1, SysConfig.ZX.allowsFormula E := by
        intro E hE
        rcases List.mem_append.mp hE with hE | hE
        · exact hΓ0 E hE
        · simp only [List.mem_singleton] at hE; subst hE; exact hGa
      have hG_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 G) :=
        Provable.ctx_hyp hΓ1 (by simp [Γ1])
      have hImp_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 (.imp G (Formula.impMany Gs' .varX))) :=
        Provable.ctx_hyp hΓ1 (by simp [Γ1, Γ0])
      have hRest_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 (Formula.impMany Gs' .varX)) :=
        Provable.ctx_mp hΓ1 hGa hRest hImp_in_1 hG_in_1
      have hRestX_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 (Formula.impMany (Gs'.map substBotWithX) .varX)) :=
        Provable.ctx_mp hΓ1 hRest hRestX (Provable.ctx_const hΓ1 ih') hRest_in_1
      have hX_in_1 : Provable SysConfig.ZX (Formula.impMany Γ1 .varX) := by
        apply Provable.ctx_apply_impMany hΓ1 hGs'Xa _ hX hRestX_in_1
        intro E hE
        exact List.mem_append_left _ (List.mem_append_right _ hE)
      have hGX_in_0 : Provable SysConfig.ZX (Formula.impMany Γ0 (.imp G .varX)) := by
        simpa [Γ1, impMany_append, Formula.impMany] using hX_in_1
      have hSubG_in_0 : Provable SysConfig.ZX (Formula.impMany Γ0 (substBotWithX G)) :=
        Provable.ctx_hyp hΓ0 (by simp [Γ0])
      have hStepG6 : Provable SysConfig.ZX (Formula.impMany Γ0 (.imp (.imp G .varX) .varX)) :=
        Provable.ctx_mp hΓ0 hGXa ((hGa.imp hX).imp hX) (Provable.ctx_const hΓ0 hG6) hSubG_in_0
      have hX_in_0 : Provable SysConfig.ZX (Formula.impMany Γ0 .varX) :=
        Provable.ctx_mp hΓ0 (hGa.imp hX) hX hStepG6 hGX_in_0
      simpa [Γ0, impMany_append, Formula.impMany] using hX_in_0

end BBS2002

theorem solution :
    (∀ D : BBS2002.Formula,
      BBS2002.IsDefiniteFormula D →
      (BBS2002.isRelevant D = true →
        BBS2002.Provable BBS2002.SysConfig.ZX
          (.imp (.imp (BBS2002.Formula.neg D) .varX) (BBS2002.substBotWithX D))) ∧
      BBS2002.Provable BBS2002.SysConfig.ZX (.imp D (BBS2002.substBotWithX D))) ∧
    (∀ G : BBS2002.Formula,
      BBS2002.IsGoalFormula G →
      (BBS2002.isIrrelevant G = true →
        BBS2002.Provable BBS2002.SysConfig.ZX (.imp (BBS2002.substBotWithX G) G)) ∧
      BBS2002.Provable BBS2002.SysConfig.ZX
        (.imp (BBS2002.substBotWithX G) (.imp (.imp G .varX) .varX))) ∧
    (∀ Gs : List BBS2002.Formula,
      (∀ G ∈ Gs, BBS2002.IsGoalFormula G) →
      BBS2002.Provable BBS2002.SysConfig.ZX
        (.imp
          (BBS2002.Formula.impMany Gs .varX)
          (BBS2002.Formula.impMany (Gs.map BBS2002.substBotWithX) .varX))) :=
  ⟨fun D hD => (BBS2002.lemma_3_1_aux D).1 hD,
   fun G hG => (BBS2002.lemma_3_1_aux G).2 hG,
   BBS2002.lemma_3_2⟩
