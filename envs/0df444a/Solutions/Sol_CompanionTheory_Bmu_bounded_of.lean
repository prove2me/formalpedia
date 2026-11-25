-- Prove2me | solution 1 for CompanionTheory.Bmu.bounded_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:16:12.109582+00:00
-- url     : https://prove2.me/submissions/d8f5982b-bfd3-4953-bd50-ce4d093a6424

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_NormPsiGen
import Theorems.Thm_CompanionTheory_Bmu_spanFam
import Theorems.Thm_CompanionTheory_Bmu_psiGen_one
import Theorems.Thm_CompanionTheory_Bmu_psiGen_cont
import Theorems.Thm_CompanionTheory_Bmu_norm_psiGen
import Theorems.Thm_CompanionTheory_Bmu_one_uw
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_continuous_ex
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace CompanionTheory.Bmu
theorem _root_.solution (hQB : QBound) (hAB : AbsBound) (hAd : AdaptExists) (hDec : Decomp) (hTB : TorBound)
    (hSp : SpanG) (hEx : ExpMem) (hRV : RootVec) : Bounded := by
  intro k r H _ _ _ σ hU hk z c hz hT hc V _ _ _ π hπ1 hπi hπc B hB heq w hw
  obtain ⟨Γ, hΓ⟩ := (hAd k r hk).2 z hz hT
  obtain ⟨d₁, X₁, hX₁, sp₁⟩ := spanFam (sUw k r z)
  obtain ⟨d₂, X₂, hX₂, sp₂⟩ := spanFam (sN k r)
  obtain ⟨e, Q, hQ, sp₃⟩ := spanFam (sQ k r Γ)
  have hX : ∀ j, InUw k r z (Fin.append X₁ X₂ j) ∨ InN k r (Fin.append X₁ X₂ j) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]; exact Or.inl (hX₁ i)
    · rw [Fin.append_right]; exact Or.inr (hX₂ i)
  have hspan : Spans (Hpk k r) (Fin.append X₁ X₂) Q := by
    intro Y hY
    obtain ⟨Y₁, Y₂, Y₃, h1, h2, h3, rfl⟩ := hSp k r z Γ hk hΓ Y hY
    obtain ⟨a₁, e₁⟩ := sp₁ Y₁ h1
    obtain ⟨a₂, e₂⟩ := sp₂ Y₂ h2
    obtain ⟨b, e₃⟩ := sp₃ Y₃ h3
    refine ⟨Fin.append a₁ a₂, b, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← e₁, ← e₂, ← e₃]
  have hχ : ∀ j, ∃ χ : ℝ → (V →L[ℂ] V), Continuous χ ∧ χ 0 = 1 ∧
      ∀ t v, IsSm (UH (Hpk k r)) σ v → B (σ (ex (Fin.append X₁ X₂ j) t) v) = χ t (B v) := by
    intro j
    rcases hX j with h | h
    · have hm := fun t => (hEx k r z _ t).1 h
      refine ⟨fun t => π (ex (Fin.append X₁ X₂ j) t), hπc.comp_continuous (continuous_ex _) hm, ?_, fun t v hv => ?_⟩
      · simp only [ex_zero, hπ1]
      · have := heq _ (hm t) 1 WeylGroupFacts.mem_n_one v hv
        rwa [Matrix.mul_one, psiGen_one hz, one_smul] at this
    · have hm := fun t => (hEx k r z _ t).2 h
      refine ⟨fun t => PI.BesselMapUniq.psiGen k r z c (ex (Fin.append X₁ X₂ j) t) • (1 : V →L[ℂ] V),
        ((psiGen_cont z c).comp (continuous_ex _)).smul continuous_const, ?_, fun t v hv => ?_⟩
      · simp only [ex_zero, psiGen_one hz, one_smul]
      · have := heq 1 (one_uw z) _ (hm t) v hv
        rw [Matrix.one_mul, hπ1] at this
        exact this
  choose χ hχc hχ0 hχe using hχ
  have hXL : ∀ j, Lie (Hpk k r) (Fin.append X₁ X₂ j) := fun j => (hX j).elim (fun h => h.1) fun h => h.1
  have hQL : ∀ i, Lie (Hpk k r) (Q i) := fun i => (hQ i).1
  obtain ⟨C, m, hC, hQ'⟩ := hQB _ _ H σ hU V B hB _ e _ Q hXL hQL hspan χ hχc hχ0 hχe
  obtain ⟨C₁, hC₁⟩ := hRV k r z Γ c hk hΓ hc
  set C₂ : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * ∑ i, ‖Γ⁻¹ * Q i * Γ‖ with hC₂
  obtain ⟨K, hK⟩ := hAB _ _ H σ hU V B hB e Q hQL C m hC hQ' (max C₁ C₂) (2 * r + k + 1) w hw
  refine ⟨K, fun g hg => ?_⟩
  obtain ⟨h, hh, m', hm', d, R, hd, hR, hg', rfl⟩ := hDec k r z Γ hk hz hΓ g hg
  set g' := Γ * dg d * R with hg'def
  have hsm : IsSm (UH (Hpk k r)) σ (σ g' w) := hw.apply hU.rep hg'
  rw [hU.rep.apply_mul (hU.rep.mul_mem _ hh.1 _ hm'.1) hg', heq h hh m' hm' _ hsm, norm_smul, norm_psiGen, one_mul,
    hπi h hh]
  have hconj : ∀ M : ℝ, 1 ≤ M → (∀ a : Fin r, d (eI k r a) ≤ M * d (nxt k r a)) →
      ∀ i, ‖g'⁻¹ * Q i * g'‖ ≤ max C₁ C₂ * M ^ (2 * r + k + 1) := by
    intro M hM hr i
    have e1 : g'⁻¹ * Q i * g' = (dg d * R)⁻¹ * (Γ⁻¹ * Q i * Γ) * (dg d * R) := by
      rw [hg'def, Matrix.mul_assoc Γ, Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    rw [e1]
    refine (hTB k r d R _ M hk hd hR hM hr (hQ i).2).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    refine le_trans ?_ (le_max_right _ _)
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun i => ‖Γ⁻¹ * Q i * Γ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
      (by positivity)
  by_cases hall : ∀ a : Fin r, d (eI k r a) / d (nxt k r a) ≤ 1
  · refine hK g' hg' 1 le_rfl (hconj 1 le_rfl fun a => ?_) (Or.inl rfl)
    exact (div_le_iff₀ (hd.1 _)).1 (hall a)
  · push Not at hall
    obtain ⟨a₁, ha₁⟩ := hall
    obtain ⟨a₀, -, ha₀⟩ := Finset.exists_max_image Finset.univ (fun a : Fin r => d (eI k r a) / d (nxt k r a))
      ⟨a₁, Finset.mem_univ _⟩
    have hM : 1 ≤ d (eI k r a₀) / d (nxt k r a₀) := ha₁.le.trans (ha₀ a₁ (Finset.mem_univ _))
    obtain ⟨Y, hY, hYn, hYe⟩ := hC₁ a₀ d R hd hR hg'
    refine hK g' hg' _ hM (hconj _ hM fun a => (div_le_iff₀ (hd.1 _)).1 (ha₀ a (Finset.mem_univ _)))
      (Or.inr ⟨Y, d (eI k r a₀) / d (nxt k r a₀), hY, hYn.trans (le_max_left _ _), le_abs_self _, fun τ u hu => ?_⟩)
    obtain ⟨hN, hψ⟩ := hYe τ
    have hinv : g'⁻¹ * g' = 1 := mul_eq_one_comm.1 (hU.grp.2.2.2 g' hg').2
    have e2 : g' * ex Y τ = 1 * (g' * ex Y τ * g'⁻¹) * g' := by
      rw [Matrix.one_mul, Matrix.mul_assoc (g' * ex Y τ), hinv, Matrix.mul_one]
    rw [e2, hU.rep.apply_mul (hU.rep.mul_mem _ hU.rep.one_mem _ hN.1) hg',
      heq 1 (one_uw z) _ hN _ (hu.apply hU.rep hg'), hπ1, hψ]
    rfl
end CompanionTheory.Bmu
