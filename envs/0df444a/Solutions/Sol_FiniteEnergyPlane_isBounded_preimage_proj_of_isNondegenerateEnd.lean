-- Prove2me | solution 1 for FiniteEnergyPlane.isBounded_preimage_proj_of_isNondegenerateEnd
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T19:50:05.113329+00:00
-- url     : https://prove2.me/submissions/8fce8461-6d1f-4e2e-8dab-ca212b432cb7

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib



namespace FiniteEnergyPlane

open scoped Real

theorem emb_exists_cylInf_eq (z : ℂ) (hz : z ≠ 0) :
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

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isBounded_preimage_proj_of_isNondegenerateEnd_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (u : ℂ → V n)
    (huP : IsNondegenerateEnd H u cylInf P 1) (K : Set (V n)) (hK : IsCompact K)
    (hKP : Disjoint K (Set.range P.x)) :
    Bornology.IsBounded ((proj H ∘ u) ⁻¹' K) := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  obtain ⟨d, c, b, hb, -, hw⟩ := huP
  have hxc : Continuous P.x :=
    continuous_iff_continuousAt.2 fun τ => (P.hasDerivAt τ).continuousAt
  have hper : Function.Periodic P.x P.T := P.periodic
  have hRc : IsCompact (Set.range P.x) := hper.compact_of_continuous P.T_pos.ne' hxc
  have hRne : (Set.range P.x).Nonempty := ⟨P.x 0, 0, rfl⟩
  obtain ⟨y₀, hy₀K, hmin⟩ := hK.exists_isMinOn hKne
    ((continuous_infDist_pt (Set.range P.x)).continuousOn)
  set δ := infDist y₀ (Set.range P.x) with hδ
  have hδpos : 0 < δ :=
    (hRc.isClosed.notMem_iff_infDist_pos hRne).1 (Set.disjoint_left.1 hKP hy₀K)
  obtain ⟨s₀, hs₀⟩ := hw (δ / 2) (by linarith)
  set s₁ := max s₀ 0 with hs₁
  refine (isBounded_closedBall (x := (0 : ℂ)) (r := Real.exp (2 * π * s₁))).subset ?_
  intro z hz
  rw [mem_closedBall_zero_iff]
  by_contra hlt
  push_neg at hlt
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hlt; exact (Real.exp_pos _).not_ge hlt.le
  set s := Real.log ‖z‖ / (2 * π) with hsdef
  obtain ⟨t, ht⟩ := emb_exists_cylInf_eq z hz0
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hss : s₁ < s := by
    rw [hsdef, lt_div_iff₀ (by positivity)]
    have := Real.log_lt_log (Real.exp_pos _) hlt
    rw [Real.log_exp] at this
    linarith
  have h1 := hs₀ s (le_trans (le_max_left _ _) hss.le) t
  have hsn : 0 ≤ s := le_trans (le_max_right _ _) hss.le
  have hge : 1 ≤ Real.exp (b * s) := Real.one_le_exp (mul_nonneg hb.le hsn)
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
  have h2 : ‖endW H u cylInf (s, t) - P.x (1 * P.T * (s, t).2 + c)‖ ≤ δ / 2 := by
    have hn := norm_nonneg (endW H u cylInf (s, t) - P.x (1 * P.T * (s, t).2 + c))
    nlinarith
  have hW : endW H u cylInf (s, t) = proj H (u z) := by
    simp only [endW]; rw [ht]
  rw [hW] at h2
  have h3 : infDist (proj H (u z)) (Set.range P.x) ≤ δ / 2 :=
    (infDist_le_dist_of_mem (Set.mem_range_self (1 * P.T * (s, t).2 + c))).trans (by rw [dist_eq_norm]; exact h2)
  have h4 : δ ≤ infDist (proj H (u z)) (Set.range P.x) := hmin hz
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (u : ℂ → V n)
    (huP : IsNondegenerateEnd H u cylInf P 1) (K : Set (V n)) (hK : IsCompact K)
    (hKP : Disjoint K (Set.range P.x)) :
    Bornology.IsBounded ((proj H ∘ u) ⁻¹' K) :=
  isBounded_preimage_proj_of_isNondegenerateEnd_aux H hH P u huP K hK hKP
