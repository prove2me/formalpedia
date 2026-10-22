-- Prove2me | solution 1 for BellmanIneq.Regret.theorem_5_compensated_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T02:44:45.238156+00:00
-- url     : https://prove2.me/submissions/97342e9a-e387-41e4-8875-4e7fbfc8fb34

import Definitions.Def_BellmanIneq_Regret_Policy
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_BellmanIneq_Regret_theorem_5_maxloss_step

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace BellmanIneq.Regret.BIAux

open MeasureTheory

theorem meas_comp {α β γ : Type*} {m : MeasurableSpace α} [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] [MeasurableSpace γ]
    (X : α → β) (hX : Measurable[m] X) (f : β → α → γ) (hf : ∀ b, Measurable[m] (f b)) :
    Measurable[m] (fun a => f (X a) a) := by
  intro B hB
  have : (fun a => f (X a) a) ⁻¹' B = ⋃ b, X ⁻¹' {b} ∩ f b ⁻¹' B := by
    ext a; simp
  rw [this]
  exact MeasurableSet.iUnion fun b => (hX (measurableSet_singleton b)).inter (hf b hB)

theorem condExp_comp {α β : Type*} {m0 : MeasurableSpace α} {μ : @Measure α m0}
    (m : MeasurableSpace α) [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    (X : α → β) (hX : Measurable[m] X) (g : β → α → ℝ)
    (hgint : ∀ b, Integrable (g b) μ) (hint : Integrable (fun a => g (X a) a) μ) :
    μ[fun a => g (X a) a | m] =ᵐ[μ] fun a => μ[g (X a) | m] a := by
  have key : ∀ b, ∀ᵐ a ∂μ, X a = b → μ[fun a => g (X a) a | m] a = μ[g b | m] a := by
    intro b
    have hs : MeasurableSet[m] (X ⁻¹' {b}) := hX (measurableSet_singleton b)
    have h1 := condExp_indicator (m := m) hint hs
    have h3 := condExp_indicator (m := m) (hgint b) hs
    have h2 : (X ⁻¹' {b}).indicator (fun a => g (X a) a) = (X ⁻¹' {b}).indicator (g b) := by
      funext a
      by_cases ha : a ∈ X ⁻¹' {b}
      · have : X a = b := ha
        simp [Set.indicator_of_mem ha, this]
      · simp [Set.indicator_of_notMem ha]
    rw [h2] at h1
    filter_upwards [h1, h3] with a h1a h3a hXa
    have hmem : a ∈ X ⁻¹' {b} := hXa
    have := h1a.symm.trans h3a
    simpa [Set.indicator_of_mem hmem] using this
  have := ae_all_iff.mpr key
  filter_upwards [this] with a ha
  exact ha (X a) rfl

variable {Ω S Ξ U : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]

theorem observed_anti (ξ : ℕ → Ω → Ξ) (T : ℕ) {a b : ℕ} (h : a ≤ b) :
    observed ξ T b ≤ observed ξ T a := by
  unfold observed
  refine iSup₂_le fun l hl => ?_
  have : l ∈ Finset.Icc (max 1 a) T := by
    simp only [Finset.mem_Icc, max_le_iff] at hl ⊢; omega
  exact le_iSup₂ (f := fun l (_ : l ∈ Finset.Icc (max 1 a) T) =>
    MeasurableSpace.comap (ξ l) mΞ) l this

theorem augmented_anti (ξ : ℕ → Ω → Ξ) (T : ℕ) (Gextra : MeasurableSpace Ω) {a b : ℕ}
    (h : a ≤ b) : augmented ξ T Gextra b ≤ augmented ξ T Gextra a :=
  sup_le_sup_right (observed_anti ξ T h) _

theorem observed_le (ξ : ℕ → Ω → Ξ) (T : ℕ)
    (hξ : ∀ t ∈ Finset.Icc 1 T, Measurable[mΩ] (ξ t)) (t : ℕ) : observed ξ T t ≤ mΩ := by
  unfold observed
  refine iSup₂_le fun l hl => ?_
  have : l ∈ Finset.Icc 1 T := by
    simp only [Finset.mem_Icc, max_le_iff] at hl ⊢; omega
  exact measurable_iff_comap_le.mp (hξ l this)

theorem augmented_le (ξ : ℕ → Ω → Ξ) (T : ℕ) (Gextra : MeasurableSpace Ω) (hG : Gextra ≤ mΩ)
    (hξ : ∀ t ∈ Finset.Icc 1 T, Measurable[mΩ] (ξ t)) (t : ℕ) :
    augmented ξ T Gextra t ≤ mΩ :=
  sup_le (@observed_le Ω Ξ mΩ mΞ ξ T hξ t) hG

theorem xi_meas_observed (ξ : ℕ → Ω → Ξ) (T t : ℕ) (ht : t ∈ Finset.Icc 1 T) :
    Measurable[observed ξ T t] (ξ t) := by
  refine measurable_iff_comap_le.mpr ?_
  have : t ∈ Finset.Icc (max 1 t) T := by
    simp only [Finset.mem_Icc, max_le_iff] at ht ⊢; omega
  exact le_iSup₂ (f := fun l (_ : l ∈ Finset.Icc (max 1 t) T) =>
    MeasurableSpace.comap (ξ l) mΞ) t this

theorem xi_meas_augmented (ξ : ℕ → Ω → Ξ) (T t : ℕ) (Gextra : MeasurableSpace Ω)
    (ht : t ∈ Finset.Icc 1 T) :
    Measurable[augmented ξ T Gextra t] (ξ t) :=
  (xi_meas_observed ξ T t ht).mono le_sup_left le_rfl

theorem elapsed_succ (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ) (π : Policy Ω S U) (s₀ : S)
    (n : ℕ) (ω : Ω) :
    elapsedState P ξ T π s₀ (n + 1) ω =
      P.trans (elapsedState P ξ T π s₀ n ω) (ξ (T - n) ω)
        (π (T - n) (elapsedState P ξ T π s₀ n ω) ω) := rfl

theorem traj_top (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ) (π : Policy Ω S U) (s₀ : S)
    (ω : Ω) : traj P ξ T π s₀ T ω = s₀ := by
  show elapsedState P ξ T π s₀ (T - T) ω = s₀
  rw [Nat.sub_self]; rfl

theorem traj_pred (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ) (π : Policy Ω S U) (s₀ : S)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 T) (ω : Ω) :
    traj P ξ T π s₀ (t - 1) ω =
      P.trans (traj P ξ T π s₀ t ω) (ξ t ω) (act P ξ T π s₀ t ω) := by
  simp only [Finset.mem_Icc] at ht
  have h1 : T - (t - 1) = (T - t) + 1 := by omega
  have h2 : T - (T - t) = t := by omega
  show elapsedState P ξ T π s₀ (T - (t - 1)) ω =
    P.trans (elapsedState P ξ T π s₀ (T - t) ω) (ξ t ω)
      (π t (elapsedState P ξ T π s₀ (T - t) ω) ω)
  rw [h1, elapsed_succ, h2]

variable [mS : MeasurableSpace S] [mU : MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass U] [Countable S] [Countable U]

theorem elapsed_meas (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ) (π : Policy Ω S U) (s₀ : S)
    (M : ℕ → MeasurableSpace Ω) (hM : ∀ a b, a ≤ b → M b ≤ M a)
    (hξM : ∀ t ∈ Finset.Icc 1 T, Measurable[M t] (ξ t))
    (hπM : ∀ t ∈ Finset.Icc 1 T, ∀ s, Measurable[M t] (π t s))
    (htr : ∀ s u, Measurable (fun x => P.trans s x u)) :
    ∀ n, n ≤ T → Measurable[M (T - n + 1)] (elapsedState P ξ T π s₀ n) := by
  intro n
  induction n with
  | zero => intro _; exact measurable_const
  | succ n ih =>
    intro hn
    have hmem : T - n ∈ Finset.Icc 1 T := by simp only [Finset.mem_Icc]; omega
    have hprev : Measurable[M (T - (n + 1) + 1)] (elapsedState P ξ T π s₀ n) :=
      (ih (by omega)).mono (hM _ _ (by omega)) le_rfl
    have heq : T - (n + 1) + 1 = T - n := by omega
    rw [heq] at hprev ⊢
    show Measurable[M (T - n)] (fun ω =>
      P.trans (elapsedState P ξ T π s₀ n ω) (ξ (T - n) ω)
        (π (T - n) (elapsedState P ξ T π s₀ n ω) ω))
    refine meas_comp (m := M (T - n)) _ hprev
      (fun s ω => P.trans s (ξ (T - n) ω) (π (T - n) s ω)) fun s => ?_
    exact meas_comp (m := M (T - n)) _ (hπM _ hmem s) (fun u ω => P.trans s (ξ (T - n) ω) u)
      fun u => (htr s u).comp (hξM _ hmem)

theorem traj_meas (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ) (π : Policy Ω S U) (s₀ : S)
    (M : ℕ → MeasurableSpace Ω) (hM : ∀ a b, a ≤ b → M b ≤ M a)
    (hξM : ∀ t ∈ Finset.Icc 1 T, Measurable[M t] (ξ t))
    (hπM : ∀ t ∈ Finset.Icc 1 T, ∀ s, Measurable[M t] (π t s))
    (htr : ∀ s u, Measurable (fun x => P.trans s x u)) (t : ℕ) (ht : t ≤ T) :
    Measurable[M t] (traj P ξ T π s₀ t) := by
  have := elapsed_meas P ξ T π s₀ M hM hξM hπM htr (T - t) (by omega)
  have heq : T - (T - t) + 1 = t + 1 := by omega
  rw [heq] at this
  exact this.mono (hM _ _ (by omega)) le_rfl

theorem act_meas (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ) (π : Policy Ω S U) (s₀ : S)
    (M : ℕ → MeasurableSpace Ω) (hM : ∀ a b, a ≤ b → M b ≤ M a)
    (hξM : ∀ t ∈ Finset.Icc 1 T, Measurable[M t] (ξ t))
    (hπM : ∀ t ∈ Finset.Icc 1 T, ∀ s, Measurable[M t] (π t s))
    (htr : ∀ s u, Measurable (fun x => P.trans s x u)) (t : ℕ) (ht : t ∈ Finset.Icc 1 T) :
    Measurable[M t] (act P ξ T π s₀ t) := by
  have ht' : t ≤ T := (Finset.mem_Icc.mp ht).2
  exact meas_comp (m := M t) _ (traj_meas P ξ T π s₀ M hM hξM hπM htr t ht')
    (fun s ω => π t s ω) fun s => hπM t ht s


theorem integrable_of_meas_bdd {α : Type*} {m0 : MeasurableSpace α} {μ : @Measure α m0}
    [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable[m0] f) (C : ℝ) (hC : ∀ a, |f a| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun a => by simpa [Real.norm_eq_abs] using hC a)

/-- Measurability of `ω ↦ ϕ t (X ω) ω` for a measurable state process `X`. -/
theorem phi_comp_meas (ψ : S → Ω → ℝ) (M : MeasurableSpace Ω)
    (hψ : ∀ s, StronglyMeasurable[M] (ψ s)) (X : Ω → S) (hX : Measurable[M] X) :
    Measurable[M] (fun ω => ψ (X ω) ω) :=
  meas_comp (m := M) X hX ψ fun s => (hψ s).measurable

theorem pull_cont {K : ℝ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ) (Gextra : MeasurableSpace Ω)
    (ϕ : ℕ → S → Ω → ℝ) (π : Policy Ω S U) (s₀ : S)
    (hG : Gextra ≤ mΩ) (hξ : ∀ t ∈ Finset.Icc 1 T, Measurable[mΩ] (ξ t))
    (htr : ∀ s u, Measurable (fun x => P.trans s x u))
    (hπM : ∀ t ∈ Finset.Icc 1 T, ∀ s, Measurable[augmented ξ T Gextra t] (π t s))
    (t : ℕ) (ht : t ∈ Finset.Icc 1 T)
    (hϕm : ∀ s, StronglyMeasurable[augmented ξ T Gextra (t - 1)] (ϕ (t - 1) s))
    (hϕb : ∀ s ω, |ϕ (t - 1) s ω| ≤ K) :
    μ[fun ω => ϕ (t - 1) (traj P ξ T π s₀ (t - 1) ω) ω | augmented ξ T Gextra t] =ᵐ[μ]
      fun ω => @cont Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ t (traj P ξ T π s₀ t ω)
        (act P ξ T π s₀ t ω) ω := by
  have hM : ∀ a b, a ≤ b → augmented ξ T Gextra b ≤ augmented ξ T Gextra a :=
    fun a b h => augmented_anti ξ T Gextra h
  have hξM : ∀ t ∈ Finset.Icc 1 T, Measurable[augmented ξ T Gextra t] (ξ t) :=
    fun t ht => xi_meas_augmented ξ T t Gextra ht
  have ht' : t ≤ T := (Finset.mem_Icc.mp ht).2
  have hS := traj_meas P ξ T π s₀ (augmented ξ T Gextra) hM hξM hπM htr t ht'
  have hA := act_meas P ξ T π s₀ (augmented ξ T Gextra) hM hξM hπM htr t ht
  have hle : augmented ξ T Gextra (t - 1) ≤ mΩ := @augmented_le Ω Ξ mΩ mΞ ξ T Gextra hG hξ (t - 1)
  have hle' : augmented ξ T Gextra t ≤ mΩ := @augmented_le Ω Ξ mΩ mΞ ξ T Gextra hG hξ t
  have hξt : Measurable[mΩ] (ξ t) := hξ t ht
  let g : S × U → Ω → ℝ := fun p ω => ϕ (t - 1) (P.trans p.1 (ξ t ω) p.2) ω
  have hgm : ∀ p : S × U, Measurable[mΩ] (g p) := fun p =>
    meas_comp (m := mΩ) (fun ω => P.trans p.1 (ξ t ω) p.2) ((htr p.1 p.2).comp hξt)
      (ϕ (t - 1)) fun s => ((hϕm s).measurable.mono hle le_rfl)
  have hgint : ∀ p, Integrable (g p) μ := fun p =>
    integrable_of_meas_bdd _ (hgm p) K fun ω => hϕb _ ω
  let X : Ω → S × U := fun ω => (traj P ξ T π s₀ t ω, act P ξ T π s₀ t ω)
  have hX : Measurable[augmented ξ T Gextra t] X := hS.prodMk hA
  have hXm : Measurable[mΩ] X := hX.mono hle' le_rfl
  have hint : Integrable (fun ω => g (X ω) ω) μ :=
    integrable_of_meas_bdd _ (meas_comp (m := mΩ) X hXm g hgm) K fun ω => hϕb _ ω
  have hfun : (fun ω => ϕ (t - 1) (traj P ξ T π s₀ (t - 1) ω) ω) = fun ω => g (X ω) ω := by
    funext ω
    simp only [g, X]
    rw [traj_pred P ξ T π s₀ ht ω]
  rw [hfun]
  exact condExp_comp (augmented ξ T Gextra t) X hX g hgint hint

section Facts
variable {K : ℝ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ) (Gextra : MeasurableSpace Ω)
    (ϕ LB : ℕ → S → Ω → ℝ) (π : Policy Ω S U) (s₀ : S)

theorem state_facts
    (hG : Gextra ≤ mΩ) (hξ : ∀ t ∈ Finset.Icc 1 T, Measurable[mΩ] (ξ t))
    (hP : P.Standing K)
    (hBI : @BellmanInequalities Ω S Ξ U mΩ mΞ μ P ξ T Gextra K ϕ LB s₀)
    (hπM : ∀ t ∈ Finset.Icc 1 T, ∀ s, Measurable[augmented ξ T Gextra t] (π t s))
    (t : ℕ) (ht : t ∈ Finset.Icc 0 T) :
    Integrable (fun ω => ϕ t (traj P ξ T π s₀ t ω) ω) μ ∧
    Integrable (fun ω => LB t (traj P ξ T π s₀ t ω) ω) μ := by
  have hM : ∀ a b, a ≤ b → augmented ξ T Gextra b ≤ augmented ξ T Gextra a :=
    fun a b h => augmented_anti ξ T Gextra h
  have hξM : ∀ t ∈ Finset.Icc 1 T, Measurable[augmented ξ T Gextra t] (ξ t) :=
    fun t ht => xi_meas_augmented ξ T t Gextra ht
  have hm : augmented ξ T Gextra t ≤ mΩ := @augmented_le Ω Ξ mΩ mΞ ξ T Gextra hG hξ t
  have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
  have hS := traj_meas P ξ T π s₀ (augmented ξ T Gextra) hM hξM hπM hP.2.2.2.1 t htT
  have hϕS := phi_comp_meas (ϕ t) _ (hBI.1 t ht) _ hS
  have hLBS := phi_comp_meas (LB t) _ (hBI.2.1 t ht) _ hS
  exact ⟨integrable_of_meas_bdd _ (hϕS.mono hm le_rfl) K fun ω => (hBI.2.2.1 t ht _ ω).1,
    integrable_of_meas_bdd _ (hLBS.mono hm le_rfl) K fun ω => (hBI.2.2.1 t ht _ ω).2⟩

theorem step_facts
    (hG : Gextra ≤ mΩ) (hξ : ∀ t ∈ Finset.Icc 1 T, Measurable[mΩ] (ξ t))
    (hP : P.Standing K)
    (hBI : @BellmanInequalities Ω S Ξ U mΩ mΞ μ P ξ T Gextra K ϕ LB s₀)
    (hπM : ∀ t ∈ Finset.Icc 1 T, ∀ s, Measurable[augmented ξ T Gextra t] (π t s))
    (hπ : Feasible P ξ T π) (r : ℝ)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 T) :
    MeasurableSet[mΩ] (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t) ∧
    Integrable (fun ω => P.R (traj P ξ T π s₀ t ω) (ξ t ω) (act P ξ T π s₀ t ω)) μ ∧
    Integrable (fun ω => r * (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t).indicator
      (fun _ => (1 : ℝ)) ω + (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t)ᶜ.indicator
      (fun ω => LB t (traj P ξ T π s₀ t ω) ω) ω) μ := by
  have hM : ∀ a b, a ≤ b → augmented ξ T Gextra b ≤ augmented ξ T Gextra a :=
    fun a b h => augmented_anti ξ T Gextra h
  have hξM : ∀ t ∈ Finset.Icc 1 T, Measurable[augmented ξ T Gextra t] (ξ t) :=
    fun t ht => xi_meas_augmented ξ T t Gextra ht
  have hm : augmented ξ T Gextra t ≤ mΩ := @augmented_le Ω Ξ mΩ mΞ ξ T Gextra hG hξ t
  have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
  have ht0 : t ∈ Finset.Icc 0 T := by simp only [Finset.mem_Icc] at ht ⊢; omega
  have hS := traj_meas P ξ T π s₀ (augmented ξ T Gextra) hM hξM hπM hP.2.2.2.1 t htT
  have hA := act_meas P ξ T π s₀ (augmented ξ T Gextra) hM hξM hπM hP.2.2.2.1 t ht
  have hX : Measurable[augmented ξ T Gextra t]
      (fun ω => (traj P ξ T π s₀ t ω, act P ξ T π s₀ t ω)) := hS.prodMk hA
  have hRf : Measurable[augmented ξ T Gextra t]
      (fun ω => P.R (traj P ξ T π s₀ t ω) (ξ t ω) (act P ξ T π s₀ t ω)) :=
    meas_comp (m := augmented ξ T Gextra t) _ hX (fun p ω => P.R p.1 (ξ t ω) p.2)
      fun p => (hP.2.2.1 p.1 p.2).comp (hξM t ht)
  have hcont : Measurable[augmented ξ T Gextra t] (fun ω =>
      @cont Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ t (traj P ξ T π s₀ t ω) (act P ξ T π s₀ t ω) ω) :=
    meas_comp (m := augmented ξ T Gextra t) _ hX
      (fun p => @cont Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ t p.1 p.2)
      fun p => stronglyMeasurable_condExp.measurable
  have hϕS := phi_comp_meas (ϕ t) _ (hBI.1 t ht0) _ hS
  have hLBS := phi_comp_meas (LB t) _ (hBI.2.1 t ht0) _ hS
  have hQ : MeasurableSet[augmented ξ T Gextra t]
      (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t) :=
    (measurableSet_le hϕS ((hRf.add hcont).add hLBS)).compl
  refine ⟨hm _ hQ, ?_, ?_⟩
  · exact integrable_of_meas_bdd _ (hRf.mono hm le_rfl) K fun ω =>
      hP.2.2.2.2.2 _ _ _ (hπ t ht _ ω)
  · have hCf : Measurable[augmented ξ T Gextra t] (fun ω => r *
        (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t).indicator (fun _ => (1 : ℝ)) ω +
        (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t)ᶜ.indicator
          (fun ω => LB t (traj P ξ T π s₀ t ω) ω) ω) :=
      (measurable_const.mul (measurable_const.indicator hQ)).add (hLBS.indicator hQ.compl)
    refine integrable_of_meas_bdd _ (hCf.mono hm le_rfl) (|r| + K) fun ω => ?_
    have hK : |LB t (traj P ξ T π s₀ t ω) ω| ≤ K := (hBI.2.2.1 t ht0 _ ω).2
    have hK0 : 0 ≤ K := hP.1
    by_cases hω : ω ∈ @disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t
    · simp only [Set.indicator_of_mem hω,
        Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hω)]
      simp; linarith [abs_nonneg r]
    · simp only [Set.indicator_of_notMem hω, Set.indicator_of_mem (Set.mem_compl hω)]
      simp; linarith [abs_nonneg r]

end Facts

end BellmanIneq.Regret.BIAux


open BellmanIneq.Regret BellmanIneq.Regret.BIAux MeasureTheory

section
variable {Ω S Ξ U : Type*}
variable [mΩ : MeasurableSpace Ω] [mS : MeasurableSpace S]
variable [mΞ : MeasurableSpace Ξ] [mU : MeasurableSpace U]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass U]
variable [Countable S] [Fintype U] [Nonempty U]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ)
variable (Gextra : MeasurableSpace Ω) (K : ℝ)
variable (ϕ LB : ℕ → S → Ω → ℝ) (s₀ : S)

theorem solution
    (hG : Gextra ≤ mΩ) (hξ : ∀ t ∈ Finset.Icc 1 T, Measurable[mΩ] (ξ t))
    (hP : P.Standing K)
    (hBI : @BellmanInequalities Ω S Ξ U mΩ mΞ μ P ξ T Gextra K ϕ LB s₀)
    (r : ℝ) (hr : @MaxLossBound Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ r)
    (π : Policy Ω S U)
    (hπF : NonAnticipative ξ T π)
    (hπ : Feasible P ξ T π) :
    ∀ t ∈ Finset.Icc 1 T,
      (fun ω => ϕ t (traj P ξ T π s₀ t ω) ω) ≤ᵐ[μ]
        μ[fun ω => P.R (traj P ξ T π s₀ t ω) (ξ t ω) (act P ξ T π s₀ t ω) + ϕ (t - 1) (traj P ξ T π s₀ (t - 1) ω) ω + (r * (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t).indicator (fun _ => (1 : ℝ)) ω + (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t)ᶜ.indicator (fun ω => LB t (traj P ξ T π s₀ t ω) ω) ω) |
          augmented ξ T Gextra t] := by
  intro t ht
  have hmax := theorem_5_maxloss_step (mΩ := mΩ) (mS := mS) (mΞ := mΞ) (mU := mU)
    μ P ξ T Gextra K ϕ LB s₀ hG hξ hP hBI r hr π hπF hπ t ht
  have hπM : ∀ t ∈ Finset.Icc 1 T, ∀ s, Measurable[augmented ξ T Gextra t] (π t s) :=
    fun t ht s => (hπF t ht s).mono le_sup_left le_rfl
  have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
  have ht0 : t ∈ Finset.Icc 0 T := by simp only [Finset.mem_Icc] at ht ⊢; omega
  have ht1 : t - 1 ∈ Finset.Icc 0 T := by
    simp only [Finset.mem_Icc] at ht ⊢; omega
  have hpull := @pull_cont Ω S Ξ U mΩ mΞ mS mU _ _ _ _ K μ _ P ξ T Gextra ϕ π s₀ hG hξ
    hP.2.2.2.1 hπM t ht (hBI.1 (t - 1) ht1) (fun s ω => (hBI.2.2.1 (t - 1) ht1 s ω).1)
  have hM : ∀ a b, a ≤ b → augmented ξ T Gextra b ≤ augmented ξ T Gextra a :=
    fun a b h => augmented_anti ξ T Gextra h
  have hξM : ∀ t ∈ Finset.Icc 1 T, Measurable[augmented ξ T Gextra t] (ξ t) :=
    fun t ht => xi_meas_augmented ξ T t Gextra ht
  have hm : augmented ξ T Gextra t ≤ mΩ := @augmented_le Ω Ξ mΩ mΞ ξ T Gextra hG hξ t
  have hm1 : augmented ξ T Gextra (t - 1) ≤ mΩ := @augmented_le Ω Ξ mΩ mΞ ξ T Gextra hG hξ (t - 1)
  have hS := traj_meas P ξ T π s₀ (augmented ξ T Gextra) hM hξM hπM hP.2.2.2.1 t htT
  have hS1 : Measurable[mΩ] (traj P ξ T π s₀ (t - 1)) :=
    (traj_meas P ξ T π s₀ (augmented ξ T Gextra) hM hξM hπM hP.2.2.2.1 (t - 1)
      (by omega)).mono hm1 le_rfl
  have hA := act_meas P ξ T π s₀ (augmented ξ T Gextra) hM hξM hπM hP.2.2.2.1 t ht
  have hX : Measurable[augmented ξ T Gextra t]
      (fun ω => (traj P ξ T π s₀ t ω, act P ξ T π s₀ t ω)) := hS.prodMk hA
  let Rf : Ω → ℝ := fun ω => P.R (traj P ξ T π s₀ t ω) (ξ t ω) (act P ξ T π s₀ t ω)
  let Bf : Ω → ℝ := fun ω => ϕ (t - 1) (traj P ξ T π s₀ (t - 1) ω) ω
  let Q := @disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t
  let Cf : Ω → ℝ := fun ω => r * Q.indicator (fun _ => (1 : ℝ)) ω +
    Qᶜ.indicator (fun ω => LB t (traj P ξ T π s₀ t ω) ω) ω
  show (fun ω => ϕ t (traj P ξ T π s₀ t ω) ω) ≤ᵐ[μ] μ[Rf + Bf + Cf | augmented ξ T Gextra t]
  have hRf : Measurable[augmented ξ T Gextra t] Rf :=
    meas_comp (m := augmented ξ T Gextra t) _ hX (fun p ω => P.R p.1 (ξ t ω) p.2)
      fun p => (hP.2.2.1 p.1 p.2).comp (hξM t ht)
  have hcont : Measurable[augmented ξ T Gextra t] (fun ω =>
      @cont Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ t (traj P ξ T π s₀ t ω) (act P ξ T π s₀ t ω) ω) :=
    meas_comp (m := augmented ξ T Gextra t) _ hX
      (fun p => @cont Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ t p.1 p.2)
      fun p => stronglyMeasurable_condExp.measurable
  have hϕS := phi_comp_meas (ϕ t) _ (hBI.1 t ht0) _ hS
  have hLBS := phi_comp_meas (LB t) _ (hBI.2.1 t ht0) _ hS
  have hQ : MeasurableSet[augmented ξ T Gextra t] Q :=
    (measurableSet_le hϕS ((hRf.add hcont).add hLBS)).compl
  have hCf : Measurable[augmented ξ T Gextra t] Cf :=
    (measurable_const.mul (measurable_const.indicator hQ)).add (hLBS.indicator hQ.compl)
  have hBf : Measurable[mΩ] Bf :=
    phi_comp_meas (ϕ (t - 1)) mΩ (fun s => (hBI.1 (t - 1) ht1 s).mono hm1) _ hS1
  have hRint : Integrable Rf μ :=
    integrable_of_meas_bdd _ (hRf.mono hm le_rfl) K fun ω =>
      hP.2.2.2.2.2 _ _ _ (hπ t ht _ ω)
  have hBint : Integrable Bf μ :=
    integrable_of_meas_bdd _ hBf K fun ω => (hBI.2.2.1 (t - 1) ht1 _ ω).1
  have hCint : Integrable Cf μ := by
    refine integrable_of_meas_bdd _ (hCf.mono hm le_rfl) (|r| + K) fun ω => ?_
    have hK : |LB t (traj P ξ T π s₀ t ω) ω| ≤ K := (hBI.2.2.1 t ht0 _ ω).2
    have hK0 : 0 ≤ K := hP.1
    by_cases hω : ω ∈ Q
    · simp only [Cf, Set.indicator_of_mem hω, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hω)]
      simp; linarith [abs_nonneg r]
    · simp only [Cf, Set.indicator_of_notMem hω, Set.indicator_of_mem (Set.mem_compl hω)]
      simp; linarith [abs_nonneg r]
  have hRce : μ[Rf | augmented ξ T Gextra t] = Rf :=
    condExp_of_stronglyMeasurable hm hRf.stronglyMeasurable hRint
  have hCce : μ[Cf | augmented ξ T Gextra t] = Cf :=
    condExp_of_stronglyMeasurable hm hCf.stronglyMeasurable hCint
  have hadd1 := condExp_add (hRint.add hBint) hCint (augmented ξ T Gextra t)
  have hadd2 := condExp_add hRint hBint (augmented ξ T Gextra t)
  filter_upwards [hadd1, hadd2, hpull, hmax] with ω h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.add_apply, hRce, hCce]
  rw [hRce] at h2
  by_cases hω : ω ∈ Q
  · have := h4 hω
    simp only [Cf, Set.indicator_of_mem hω, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hω)]
    simp only [Rf] at this ⊢
    linarith
  · have hsat : ϕ t (traj P ξ T π s₀ t ω) ω ≤
        P.R (traj P ξ T π s₀ t ω) (ξ t ω) (act P ξ T π s₀ t ω) +
          @cont Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ t (traj P ξ T π s₀ t ω)
            (act P ξ T π s₀ t ω) ω + LB t (traj P ξ T π s₀ t ω) ω := by
      by_contra hc; exact hω hc
    simp only [Cf, Set.indicator_of_notMem hω, Set.indicator_of_mem (Set.mem_compl hω)]
    simp only [Bf] at h3 ⊢
    rw [h3]
    simp only [Rf]
    linarith
end
