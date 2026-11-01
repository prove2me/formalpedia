-- Prove2me | solution 1 for BBS2002.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:24:20.87488+00:00
-- url     : https://prove2.me/submissions/c505fc37-611d-43cb-8e2c-fa68bf0973f6

import Definitions.Def_BBS2002_Extraction
import Theorems.Thm_BBS2002_lemma_3_1_and_3_2

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

theorem SysConfig.allowsFormula.allMany {sys : SysConfig} (ys : List Var) {A : Formula}
    (hA : sys.allowsFormula A) :
    sys.allowsFormula (Formula.allMany ys A) := by
  induction ys with
  | nil => exact hA
  | cons y ys ih => exact ih.all y

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

theorem Provable.allMany_congr {sys : SysConfig} (ys : List Var) {A B : Formula}
    (hA : sys.allowsFormula A) (hB : sys.allowsFormula B)
    (h : Provable sys (.imp A B)) :
    Provable sys (.imp (Formula.allMany ys A) (Formula.allMany ys B)) := by
  induction ys with
  | nil => exact h
  | cons y ys ih =>
      exact Provable.all_congr y (.allMany ys hA) (.allMany ys hB) ih

/-! ## Properties of `substBotWithX` and `substBotProof` -/

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
  ⟨hA.1.substBotWithX, .inl rfl⟩

theorem Derivable.substBotProof {M : ProofTerm} {A : Formula}
    (h : Derivable SysConfig.Z0 M A) :
    Derivable SysConfig.ZX (BBS2002.substBotProof M) (substBotWithX A) := by
  induction h with
  | assump u hu =>
      exact .assump ⟨u.id, substBotWithX u.formula⟩ hu.substBotWithX_ZX
  | indNat n A hn hA =>
      have h0 := Derivable.indNat (sys := SysConfig.ZX) n (substBotWithX A) hn
        hA.substBotWithX_ZX
      simpa [BBS2002.substBotProof, indNatFormula, substFormula_substBotWithX] using h0
  | indBool p A hp hA =>
      have h0 := Derivable.indBool (sys := SysConfig.ZX) p (substBotWithX A) hp
        hA.substBotWithX_ZX
      simpa [BBS2002.substBotProof, indBoolFormula, substFormula_substBotWithX] using h0
  | axTrue =>
      exact .axTrue
  | axFalse A hA =>
      exact .axFalse (substBotWithX A) hA.substBotWithX_ZX
  | efq A hEfq _ =>
      cases hEfq
  | lamAssump u hu _ ih =>
      exact .lamAssump ⟨u.id, substBotWithX u.formula⟩ hu.substBotWithX_ZX ih
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
      exact .conv ih hB.substBotWithX_ZX heq.substBotWithX

theorem Provable.substBotProof {A : Formula} (h : Provable SysConfig.Z0 A) :
    Provable SysConfig.ZX (substBotWithX A) := by
  rcases h with ⟨M, hM, hMC⟩
  refine ⟨BBS2002.substBotProof M, hM.substBotProof, ?_⟩
  apply freeAssumpVars_eq_nil_of_forall_not_mem
  intro v hv
  rcases mem_freeAssumpVars_substBotProof hv with ⟨u, hu, _⟩
  rw [hMC] at hu
  cases hu

theorem IsDefinite_IsGoal_wf (A : Formula) :
    (IsDefiniteFormula A → FormulaWellTyped A) ∧
    (IsGoalFormula A → FormulaWellTyped A) := by
  induction A with
  | bot => exact ⟨fun _ => .bot, fun _ => .bot⟩
  | varX =>
      refine ⟨fun hD => ?_, fun hG => ?_⟩
      · cases hD with | atom hAt _ => cases hAt
      · cases hG with | atom hAt _ => cases hAt
  | atom t =>
      refine ⟨fun hD => ?_, fun hG => ?_⟩
      · cases hD with | atom _ hwf => exact hwf
      · cases hG with | atom _ hwf => exact hwf
  | imp B C ihB ihC =>
      refine ⟨fun hD => ?_, fun hG => ?_⟩
      · cases hD with
        | atom hAt _ => cases hAt
        | imp hGB hDC _ => exact .imp (ihB.2 hGB) (ihC.1 hDC)
      · cases hG with
        | atom hAt _ => cases hAt
        | imp hDB hGC _ => exact .imp (ihB.1 hDB) (ihC.2 hGC)
  | all x B ihB =>
      refine ⟨fun hD => ?_, fun hG => ?_⟩
      · cases hD with
        | atom hAt _ => cases hAt
        | all _ hDB => exact .all x (ihB.1 hDB)
      · cases hG with
        | atom hAt _ => cases hAt
        | all _ hGB _ => exact .all x (ihB.2 hGB)

theorem Provable.impMany_definite_congr (Ds : List Formula) {B' B : Formula}
    (hDs : ∀ D ∈ Ds, IsDefiniteFormula D)
    (hB' : SysConfig.ZX.allowsFormula B')
    (hB : SysConfig.ZX.allowsFormula B)
    (hBB' : Provable SysConfig.ZX (.imp B' B)) :
    Provable SysConfig.ZX
      (.imp (Formula.impMany (Ds.map substBotWithX) B') (Formula.impMany Ds B)) := by
  induction Ds with
  | nil => exact hBB'
  | cons D Ds' ih =>
      have hD : IsDefiniteFormula D := hDs D (.head _)
      have hDs' : ∀ E ∈ Ds', IsDefiniteFormula E := fun E hE => hDs E (.tail _ hE)
      have hwfD : FormulaWellTyped D := (IsDefinite_IsGoal_wf D).1 hD
      have hDa : SysConfig.ZX.allowsFormula D := .of_wf hwfD
      have hDXa : SysConfig.ZX.allowsFormula (substBotWithX D) := .of_wf hwfD.substBotWithX
      have hDs'a : ∀ E ∈ Ds', SysConfig.ZX.allowsFormula E :=
        fun E hE => .of_wf ((IsDefinite_IsGoal_wf E).1 (hDs' E hE))
      have hDs'Xa : ∀ E ∈ Ds'.map substBotWithX, SysConfig.ZX.allowsFormula E := by
        intro E hE
        rcases List.mem_map.mp hE with ⟨F, hF, rfl⟩
        exact .of_wf ((IsDefinite_IsGoal_wf F).1 (hDs' F hF)).substBotWithX
      have hRestX : SysConfig.ZX.allowsFormula (Formula.impMany (Ds'.map substBotWithX) B') :=
        .impMany hDs'Xa hB'
      have hRest : SysConfig.ZX.allowsFormula (Formula.impMany Ds' B) :=
        .impMany hDs'a hB
      have hD4 : Provable SysConfig.ZX (.imp D (substBotWithX D)) :=
        (lemma_3_1_and_3_2.1 D hD).2
      exact Provable.imp_congr hDXa hDa hRestX hRest hD4 (ih hDs')

theorem theorem_3_3_proof
    (Ds Gs : List Formula) (ys : List Var)
    (hDs : ∀ D ∈ Ds, IsDefiniteFormula D)
    (hGs : ∀ G ∈ Gs, IsGoalFormula G)
    (hZ0 : Provable SysConfig.Z0 (Formula.impMany Ds (goalImpliesBot ys Gs))) :
    Provable SysConfig.ZX (Formula.impMany Ds (goalImpliesX ys Gs)) := by
  have hX : SysConfig.ZX.allowsFormula .varX := .varX_ZX
  have hGsa : ∀ G ∈ Gs, SysConfig.ZX.allowsFormula G :=
    fun G hG => .of_wf ((IsDefinite_IsGoal_wf G).2 (hGs G hG))
  have hGsXa : ∀ E ∈ Gs.map substBotWithX, SysConfig.ZX.allowsFormula E := by
    intro E hE
    rcases List.mem_map.mp hE with ⟨G, hG, rfl⟩
    exact .of_wf ((IsDefinite_IsGoal_wf G).2 (hGs G hG)).substBotWithX
  have hImpG : SysConfig.ZX.allowsFormula (Formula.impMany Gs .varX) :=
    .impMany hGsa hX
  have hImpGX : SysConfig.ZX.allowsFormula (Formula.impMany (Gs.map substBotWithX) .varX) :=
    .impMany hGsXa hX
  have hAllG : SysConfig.ZX.allowsFormula (Formula.allMany ys (Formula.impMany Gs .varX)) :=
    .allMany ys hImpG
  have hAllGX : SysConfig.ZX.allowsFormula (Formula.allMany ys (Formula.impMany (Gs.map substBotWithX) .varX)) :=
    .allMany ys hImpGX
  have hL32 : Provable SysConfig.ZX
      (.imp (Formula.impMany Gs .varX) (Formula.impMany (Gs.map substBotWithX) .varX)) :=
    lemma_3_1_and_3_2.2.2 Gs hGs
  have hAllCongr : Provable SysConfig.ZX
      (.imp (Formula.allMany ys (Formula.impMany Gs .varX))
        (Formula.allMany ys (Formula.impMany (Gs.map substBotWithX) .varX))) :=
    Provable.allMany_congr ys hImpG hImpGX hL32
  have hGoalCongr : Provable SysConfig.ZX
      (.imp (goalImpliesX ys (Gs.map substBotWithX)) (goalImpliesX ys Gs)) :=
    Provable.imp_congr hAllGX hAllG hX hX hAllCongr (Provable.id hX)
  have hSub : Provable SysConfig.ZX
      (Formula.impMany (Ds.map substBotWithX) (goalImpliesX ys (Gs.map substBotWithX))) := by
    have h0 := hZ0.substBotProof
    simpa [substBotWithX_impMany, substBotWithX_goalImpliesBot] using h0
  have hCongrDs := Provable.impMany_definite_congr Ds hDs
    (hAllGX.imp hX) (hAllG.imp hX) hGoalCongr
  exact Provable.mp hCongrDs hSub

end BBS2002

theorem solution
    (Ds Gs : List BBS2002.Formula) (ys : List BBS2002.Var)
    (hDs : ∀ D ∈ Ds, BBS2002.IsDefiniteFormula D)
    (hGs : ∀ G ∈ Gs, BBS2002.IsGoalFormula G)
    (hZ0 : BBS2002.Provable BBS2002.SysConfig.Z0 (BBS2002.Formula.impMany Ds (BBS2002.goalImpliesBot ys Gs))) :
    BBS2002.Provable BBS2002.SysConfig.ZX (BBS2002.Formula.impMany Ds (BBS2002.goalImpliesX ys Gs)) :=
  BBS2002.theorem_3_3_proof Ds Gs ys hDs hGs hZ0
