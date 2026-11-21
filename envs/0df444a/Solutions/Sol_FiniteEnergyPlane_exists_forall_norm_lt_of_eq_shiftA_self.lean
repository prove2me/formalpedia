-- Prove2me | solution 1 for FiniteEnergyPlane.exists_forall_norm_lt_of_eq_shiftA_self
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T00:16:20.340859+00:00
-- url     : https://prove2.me/submissions/1493e186-db91-4a97-a8d1-ca5fc2a9a8b7

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_hasAsymptoticEigenvector_cylInf_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_exists_eq_of_endW_eq_of_hasAsymptoticEigenvector
import Theorems.Thm_FiniteEnergyPlane_isPrime_of_isFastPlane_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Radial scaling in the symplectization: `proj` is invariant and `a` shifts by `log c / 2`. -/
theorem ff_proj_aCoord_smul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (c : ℝ) (hc : 0 < c) (y : V n) (hy : y ≠ 0) :
    proj H (c • y) = proj H y ∧ aCoord H (c • y) = aCoord H y + Real.log c / 2 := by
  obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 y hy
  have e1 : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := ⟨r, hr0, hr1⟩
  have e2 : ∃ r : ℝ, 0 < r ∧ H (r • (c • y)) = 1 :=
    ⟨r / c, div_pos hr0 hc, by rw [smul_smul, div_mul_cancel₀ _ hc.ne']; exact hr1⟩
  have h1 : scaleToS H y = r := by
    unfold scaleToS
    rw [dif_pos e1]
    exact hru _ (Classical.choose_spec e1)
  have h2 : scaleToS H (c • y) = r / c := by
    unfold scaleToS
    rw [dif_pos e2]
    have hs2 := Classical.choose_spec e2
    have := hru (Classical.choose e2 * c) ⟨mul_pos hs2.1 hc, by rw [← smul_smul]; exact hs2.2⟩
    rw [← this, mul_div_cancel_right₀ _ hc.ne']
  refine ⟨?_, ?_⟩
  · unfold proj
    rw [h1, h2, smul_smul, div_mul_cancel₀ _ hc.ne']
  · unfold aCoord
    rw [h1, h2, Real.log_div hr0.ne' hc.ne']
    ring

theorem isNondegenerateEnd_shiftA_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (u : ℂ → V n) (hu : ∀ z, u z ≠ 0) (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) (ε : ℝ)
    (h : IsNondegenerateEnd H u e P ε) (c : ℝ) :
    IsNondegenerateEnd H (shiftA c u) e P ε := by
  obtain ⟨d, c', b, hb, h1, h2⟩ := h
  have hexp := Real.exp_pos (2 * c)
  have hs : ∀ z, proj H (shiftA c u z) = proj H (u z) ∧
      aCoord H (shiftA c u z) = aCoord H (u z) + c := by
    intro z
    have := ff_proj_aCoord_smul H hH _ hexp (u z) (hu z)
    refine ⟨this.1, ?_⟩
    have h3 := this.2
    rw [Real.log_exp] at h3
    simpa [shiftA, mul_div_assoc] using h3
  refine ⟨d + c, c', b, hb, ?_, ?_⟩
  · convert h1 using 2 with p
    simp only [endA, (hs _).2]
    ring
  · convert h2 using 3 with p
    simp only [endW, (hs _).1]

theorem isFastPlane_shiftA_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (c : ℝ) : IsFastPlane H J (shiftA c u) := by
  obtain ⟨hfe, ⟨P, hP, hnd⟩, hwind⟩ := hu
  have hexp := Real.exp_pos (2 * c)
  have h0 : ∀ z, u z ≠ 0 := fun z => hfe.2.1 z (Set.mem_univ z)
  refine ⟨?_, ⟨P, hP, isNondegenerateEnd_shiftA_aux H hH u h0 cylInf P 1 hnd c⟩, ?_⟩
  · have := (rescale_isFiniteEnergyCurve H hH J hJ Set.univ isOpen_univ u hfe 0 1 one_pos _ hexp).1
    have e : shiftA c u = fun w => Real.exp (2 * c) • u w := rfl
    rw [e]
    simpa using this
  · have hpi : piDs H (shiftA c u) = piDs H u := by
      have hw : (fun z => proj H (shiftA c u z)) = fun z => proj H (u z) := by
        funext z
        exact (ff_proj_aCoord_smul H hH _ hexp (u z) (h0 z)).1
      funext z
      have hw' : proj H (shiftA c u z) = proj H (u z) := congrFun hw z
      simp only [piDs, hw, hw']
    simpa only [HasWindPi, hpi] using hwind

end FiniteEnergyPlane

/-! Glue for F `exists_eq_of_proj_eq_of_isFastPlane` (Hryniewicz (100)). -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma pef_cylInf_rep (z : ℂ) (hz : z ≠ 0) :
    ∃ t : ℝ, cylInf (Real.log ‖z‖ / (2 * π)) t = z := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hexp : Real.exp (2 * π * (Real.log ‖z‖ / (2 * π))) = ‖z‖ := by
    rw [mul_div_cancel₀ _ h2pi.ne', Real.exp_log hzpos]
  refine ⟨Complex.arg z / (2 * π), ?_⟩
  unfold cylInf ccwLoop
  rw [hexp]
  have e : ((2 * π * (Complex.arg z / (2 * π)) : ℝ) : ℂ) = (Complex.arg z : ℂ) := by
    congr 1
    field_simp
  rw [e]
  exact Complex.norm_mul_exp_arg_mul_I z

theorem exists_eq_of_proj_eq_of_isFastPlane_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hmiss : ∀ z, proj H (u z) ∉ Set.range P.x) :
    ∃ R : ℝ, ∀ z z' : ℂ, R ≤ ‖z‖ → proj H (u z) = proj H (u z') → z = z' := by
  have hP := isPrime_of_isFastPlane_of_isNondegenerateEnd H hH J hJ u hu P huP
  obtain ⟨μ, v, hv⟩ :=
    exists_hasAsymptoticEigenvector_cylInf_of_isNondegenerateEnd H hH J hJ P u hu.1 huP
  obtain ⟨S, hS⟩ := exists_eq_of_endW_eq_of_hasAsymptoticEigenvector H hH J hJ P hP u huP μ v hv
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  set R₂ := Real.exp (2 * π * S) with hR₂
  have hR₂pos : 0 < R₂ := Real.exp_pos _
  have hu0 : ∀ z, u z ≠ 0 := fun z => hu.1.2.1 z (Set.mem_univ z)
  have hucont : Continuous u := (contDiffOn_univ.1 hu.1.1).continuous
  have hpc : Continuous fun z => proj H (u z) :=
    continuous_iff_continuousAt.2 fun z =>
      ((contDiffAt_aCoord_proj H hH (u z) (hu0 z)).2.continuousAt).comp hucont.continuousAt
  have hxc : Continuous P.x := continuous_iff_continuousAt.2 fun τ => (P.hasDerivAt τ).continuousAt
  have hrange : IsCompact (Set.range P.x) := by
    have : Set.range P.x = P.x '' Set.Icc 0 P.T := by
      ext y
      constructor
      · rintro ⟨τ, rfl⟩
        obtain ⟨σ, hσ, hfσ⟩ := (show Function.Periodic P.x P.T from P.periodic).exists_mem_Ico₀
          P.T_pos τ
        exact ⟨σ, Set.Ico_subset_Icc_self hσ, hfσ.symm⟩
      · rintro ⟨σ, -, rfl⟩; exact ⟨σ, rfl⟩
    rw [this]; exact isCompact_Icc.image hxc
  have hne : (Set.range P.x).Nonempty := ⟨P.x 0, 0, rfl⟩
  have hfpos : ∀ z, 0 < infDist (proj H (u z)) (Set.range P.x) := fun z =>
    (hrange.isClosed.notMem_iff_infDist_pos hne).1 (hmiss z)
  obtain ⟨z₀, -, hz₀⟩ := (isCompact_closedBall (0 : ℂ) R₂).exists_isMinOn
    ⟨0, mem_closedBall_self hR₂pos.le⟩
    ((continuous_infDist_pt (Set.range P.x)).comp hpc).continuousOn
  set d₀ := infDist (proj H (u z₀)) (Set.range P.x) with hd₀
  have hd₀pos : 0 < d₀ := hfpos z₀
  obtain ⟨d, c₁, b, hb, -, hw⟩ := huP
  obtain ⟨s₂, hs₂⟩ := hw (d₀ / 2) (by positivity)
  refine ⟨max (max R₂ (Real.exp (2 * π * max s₂ 0))) 1, fun z z' hz hzz' => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have hlog : ∀ (w : ℂ) (A : ℝ), 0 < ‖w‖ → Real.exp (2 * π * A) ≤ ‖w‖ →
      A ≤ Real.log ‖w‖ / (2 * π) := by
    intro w A hw hA
    rw [le_div_iff₀ h2pi, mul_comm]
    exact (Real.le_log_iff_exp_le hw).2 hA
  obtain ⟨t, ht⟩ := pef_cylInf_rep z hz0
  set s := Real.log ‖z‖ / (2 * π) with hs
  have hsS : S ≤ s := hlog z S hzpos (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hz))
  have hs2 : max s₂ 0 ≤ s :=
    hlog z _ hzpos (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hz))
  have hclose : infDist (proj H (u z)) (Set.range P.x) ≤ d₀ / 2 := by
    have h1 := hs₂ s (le_trans (le_max_left _ _) hs2) t
    have hexp : 1 ≤ Real.exp (b * s) :=
      Real.one_le_exp (mul_nonneg hb.le (le_trans (le_max_right _ _) hs2))
    simp only at h1
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
    calc infDist (proj H (u z)) (Set.range P.x)
        ≤ dist (proj H (u z)) (P.x (1 * P.T * t + c₁)) := infDist_le_dist_of_mem ⟨_, rfl⟩
      _ = ‖endW H u cylInf (s, t) - P.x (1 * P.T * t + c₁)‖ := by
          rw [dist_eq_norm]; simp only [endW, ht]
      _ ≤ Real.exp (b * s) * ‖endW H u cylInf (s, t) - P.x (1 * P.T * t + c₁)‖ :=
          le_mul_of_one_le_left (norm_nonneg _) hexp
      _ ≤ d₀ / 2 := h1
  by_cases hz' : ‖z'‖ ≤ R₂
  · exfalso
    have hmin : d₀ ≤ infDist (proj H (u z')) (Set.range P.x) :=
      hz₀ (mem_closedBall_zero_iff.2 hz')
    rw [← hzz'] at hmin
    linarith
  · push_neg at hz'
    have hz'pos : 0 < ‖z'‖ := lt_trans hR₂pos hz'
    obtain ⟨t', ht'⟩ := pef_cylInf_rep z' (norm_pos_iff.1 hz'pos)
    have hs' : S ≤ Real.log ‖z'‖ / (2 * π) := hlog z' S hz'pos hz'.le
    have := hS s _ t t' hsS hs' (by simp only [endW, ht, ht']; exact hzz')
    rw [ht, ht'] at this
    exact this

end FiniteEnergyPlane

/-! Far bound for coincidences of a fast plane with its bounded nontrivial translates. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `u z = (τ·u) w` gives equal projections and `a(u z) = a(u w) + τ`. -/
lemma mo_shift_rel (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (u : ℂ → V 1)
    (hu0 : ∀ z, u z ≠ 0) (τ : ℝ) (z w : ℂ) (h : u z = shiftA τ u w) :
    proj H (u z) = proj H (u w) ∧ aCoord H (u z) = aCoord H (u w) + τ := by
  have h' : u z = Real.exp (2 * τ) • u w := h
  obtain ⟨h1, h2⟩ := ff_proj_aCoord_smul H hH (Real.exp (2 * τ)) (Real.exp_pos _) (u w) (hu0 w)
  rw [h', h1, h2, Real.log_exp]
  exact ⟨rfl, by ring⟩

/-- `u z = (τ·u) w` with `z = w` forces `τ = 0`. -/
lemma mo_tau_eq_zero (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0) (τ : ℝ) (z : ℂ)
    (h : u z = shiftA τ u z) : τ = 0 := by
  have h' : u z = Real.exp (2 * τ) • u z := h
  have h1 : (Real.exp (2 * τ) - 1) • u z = 0 := by rw [sub_smul, one_smul, ← h', sub_self]
  rcases smul_eq_zero.1 h1 with h2 | h2
  · have : Real.exp (2 * τ) = Real.exp 0 := by rw [Real.exp_zero]; linarith
    have := Real.exp_injective this
    linarith
  · exact absurd h2 (hu0 z)

lemma mo_shift_symm (u : ℂ → V 1) (τ : ℝ) (z w : ℂ) (h : u z = shiftA τ u w) :
    u w = shiftA (-τ) u z := by
  show u w = Real.exp (2 * -τ) • u z
  have h' : u z = Real.exp (2 * τ) • u w := h
  rw [h', smul_smul, ← Real.exp_add]
  simp

theorem exists_forall_norm_lt_of_eq_shiftA_self_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∀ C : ℝ, ∃ R : ℝ, ∀ (τ : ℝ) (z w : ℂ), u z = shiftA τ u w → τ ≠ 0 → |τ| ≤ C →
      ‖z‖ < R ∧ ‖w‖ < R := by
  intro C
  have hP := isPrime_of_isFastPlane_of_isNondegenerateEnd H hH J hJ u hu P huP
  obtain ⟨μ, v, hv⟩ :=
    exists_hasAsymptoticEigenvector_cylInf_of_isNondegenerateEnd H hH J hJ P u hu.1 huP
  obtain ⟨S, hS⟩ := exists_eq_of_endW_eq_of_hasAsymptoticEigenvector H hH J hJ P hP u huP μ v hv
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  set R₂ := Real.exp (2 * π * S) with hR₂
  have hR₂pos : 0 < R₂ := Real.exp_pos _
  have hu0 : ∀ z, u z ≠ 0 := fun z => hu.1.2.1 z (Set.mem_univ z)
  have hucont : Continuous u := (contDiffOn_univ.1 hu.1.1).continuous
  have hac : Continuous fun z => aCoord H (u z) :=
    continuous_iff_continuousAt.2 fun z =>
      ((contDiffAt_aCoord_proj H hH (u z) (hu0 z)).1.continuousAt).comp hucont.continuousAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R₂).exists_bound_of_continuousOn
    (f := fun z => aCoord H (u z)) hac.continuousOn
  obtain ⟨d, c₁, b, hb, ha, -⟩ := huP
  obtain ⟨s₁, hs₁⟩ := ha 1 one_pos
  have hT := P.T_pos
  -- s₃ with T s₃ + d - 1 > M + |C|
  set s₃ := max (max s₁ S) ((M + |C| - d + 2) / P.T) with hs₃
  have hs₃T : M + |C| < P.T * s₃ + d - 1 := by
    have : (M + |C| - d + 2) / P.T ≤ s₃ := le_max_right _ _
    have := (div_le_iff₀ hT).1 this
    linarith
  set R := max (Real.exp (2 * π * s₃)) 1 with hR
  have hlog : ∀ (w : ℂ) (A : ℝ), 0 < ‖w‖ → Real.exp (2 * π * A) ≤ ‖w‖ →
      A ≤ Real.log ‖w‖ / (2 * π) := by
    intro w A hw hA
    rw [le_div_iff₀ h2pi, mul_comm]
    exact (Real.le_log_iff_exp_le hw).2 hA
  -- one-sided statement
  have key : ∀ (τ : ℝ) (z w : ℂ), u z = shiftA τ u w → τ ≠ 0 → |τ| ≤ C → ‖z‖ < R := by
    intro τ z w h hτ hτC
    by_contra hz
    push_neg at hz
    have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
    obtain ⟨t, ht⟩ := pef_cylInf_rep z (norm_pos_iff.1 hzpos)
    set s := Real.log ‖z‖ / (2 * π) with hs
    have hs3 : s₃ ≤ s := hlog z s₃ hzpos (le_trans (le_max_left _ _) hz)
    have hsS : S ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs3
    have hs1 : s₁ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs3
    have haz : P.T * s₃ + d - 1 ≤ aCoord H (u z) := by
      have h1 := hs₁ s hs1 t
      simp only [endA, ht] at h1
      have h2 := (abs_le.1 h1).1
      have : P.T * s₃ ≤ P.T * s := mul_le_mul_of_nonneg_left hs3 hT.le
      linarith
    obtain ⟨hpr, har⟩ := mo_shift_rel H hH u hu0 τ z w h
    have hτle : τ ≤ |C| := le_trans (le_abs_self τ) (le_trans hτC (le_abs_self C))
    have haw : M < aCoord H (u w) := by linarith
    have hw : R₂ < ‖w‖ := by
      by_contra hw
      push_neg at hw
      have := hM w (mem_closedBall_zero_iff.2 hw)
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (aCoord H (u w))]
    have hwpos : 0 < ‖w‖ := lt_trans hR₂pos hw
    obtain ⟨t', ht'⟩ := pef_cylInf_rep w (norm_pos_iff.1 hwpos)
    have hs' : S ≤ Real.log ‖w‖ / (2 * π) := hlog w S hwpos hw.le
    have hzw := hS s _ t t' hsS hs' (by simp only [endW, ht, ht']; exact hpr)
    rw [ht, ht'] at hzw
    rw [hzw] at h
    exact hτ (mo_tau_eq_zero u hu0 τ w h)
  refine ⟨R, fun τ z w h hτ hτC => ⟨key τ z w h hτ hτC, ?_⟩⟩
  exact key (-τ) w z (mo_shift_symm u τ z w h) (neg_ne_zero.2 hτ) (by rwa [abs_neg])

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∀ C : ℝ, ∃ R : ℝ, ∀ (τ : ℝ) (z w : ℂ), u z = shiftA τ u w → τ ≠ 0 → |τ| ≤ C →
      ‖z‖ < R ∧ ‖w‖ < R :=
  FiniteEnergyPlane.exists_forall_norm_lt_of_eq_shiftA_self_aux H hH J hJ P u hu huP
