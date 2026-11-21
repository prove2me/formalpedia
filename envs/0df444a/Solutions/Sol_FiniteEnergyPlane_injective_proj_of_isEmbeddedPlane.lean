-- Prove2me | solution 1 for FiniteEnergyPlane.injective_proj_of_isEmbeddedPlane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T00:27:18.802628+00:00
-- url     : https://prove2.me/submissions/e0d858e5-4f64-4e6c-91c3-15e09bf3658b

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_exists_forall_norm_lt_of_eq_shiftA_self
import Theorems.Thm_FiniteEnergyPlane_exists_intersection_of_tendstoCInftyLocOn
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_shiftA
import Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_shiftA
import Theorems.Thm_FiniteEnergyPlane_forall_isolated_of_isBounded_of_isClosed
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_immersion_transverse
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real
open FiniteEnergyPlane
open scoped ContDiff Topology in
open scoped ContDiff Topology

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

/-! Small helpers for Hryniewicz Lemma 6.24 (translates and local injectivity). -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma moh_shift_rel (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (u : ℂ → V 1)
    (hu0 : ∀ z, u z ≠ 0) (τ : ℝ) (z w : ℂ) (h : u z = shiftA τ u w) :
    proj H (u z) = proj H (u w) ∧ aCoord H (u z) = aCoord H (u w) + τ := by
  have h' : u z = Real.exp (2 * τ) • u w := h
  obtain ⟨h1, h2⟩ := ff_proj_aCoord_smul H hH (Real.exp (2 * τ)) (Real.exp_pos _) (u w) (hu0 w)
  rw [h', h1, h2, Real.log_exp]
  exact ⟨rfl, by ring⟩

lemma moh_tau_eq_zero (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0) (τ : ℝ) (z : ℂ)
    (h : u z = shiftA τ u z) : τ = 0 := by
  have h' : u z = Real.exp (2 * τ) • u z := h
  have h1 : (Real.exp (2 * τ) - 1) • u z = 0 := by rw [sub_smul, one_smul, ← h', sub_self]
  rcases smul_eq_zero.1 h1 with h2 | h2
  · have : Real.exp (2 * τ) = Real.exp 0 := by rw [Real.exp_zero]; linarith
    have := Real.exp_injective this
    linarith
  · exact absurd h2 (hu0 z)

lemma moh_shift_symm (u : ℂ → V 1) (τ : ℝ) (z w : ℂ) (h : u z = shiftA τ u w) :
    u w = shiftA (-τ) u z := by
  show u w = Real.exp (2 * -τ) • u z
  have h' : u z = Real.exp (2 * τ) • u w := h
  rw [h', smul_smul, ← Real.exp_add]
  simp

lemma moh_shiftA_zero {n : ℕ} (u : ℂ → V n) : shiftA 0 u = u := by
  funext z; simp [shiftA]

lemma moh_fderiv_shiftA_inj {n : ℕ} (u : ℂ → V n) (hu : ContDiff ℝ ∞ u) (c : ℝ) (z : ℂ)
    (h : Function.Injective (fderiv ℝ u z)) : Function.Injective (fderiv ℝ (shiftA c u) z) := by
  have e : shiftA c u = Real.exp (2 * c) • u := rfl
  rw [e, fderiv_const_smul (hu.differentiable (by simp) z)]
  intro a b hab
  simp only [ContinuousLinearMap.smul_apply] at hab
  exact h ((smul_right_injective _ (Real.exp_pos _).ne') hab)

/-- A `C¹` map `ℂ → E` (finite-dimensional `E`) with injective derivative at `a` is injective
near `a`. -/
lemma moh_locInj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : ℂ → E) (a : ℂ) (hf : ContDiffAt ℝ 1 f a) (hinj : Function.Injective (fderiv ℝ f a)) :
    ∃ ε > 0, Set.InjOn f (ball a ε) := by
  set D := fderiv ℝ f a with hD
  have hker : LinearMap.ker (D : ℂ →ₗ[ℝ] E) = ⊥ := LinearMap.ker_eq_bot.2 hinj
  obtain ⟨Lₗ, hL⟩ := LinearMap.exists_leftInverse_of_injective (D : ℂ →ₗ[ℝ] E) hker
  set L : E →L[ℝ] ℂ := LinearMap.toContinuousLinearMap Lₗ with hLdef
  have hLD : L.comp D = ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) := by
    ext1 v
    have := congrArg (fun g : ℂ →ₗ[ℝ] ℂ => g v) hL
    simpa [hLdef] using this
  have hs : HasStrictFDerivAt f D a := hf.hasStrictFDerivAt (by norm_num)
  have hg : HasStrictFDerivAt (fun z => L (f z))
      ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) a := by
    rw [← hLD]; exact L.hasStrictFDerivAt.comp a hs
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hg.eventually_left_inverse
  refine ⟨ε, hε, fun x hx y hy hxy => ?_⟩
  have h1 := hball x hx
  have h2 := hball y hy
  rw [← h1, ← h2, hxy]

end FiniteEnergyPlane

/-! Basic identities for the symplectization of a star-shaped level (copied, renamed, from the
`ka_*` helpers of accepted solution a386257a). -/


set_option linter.unusedSimpArgs false

def ka_sig {n : ℕ} (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

def ka_sgn {n : ℕ} (k : Fin (2 * (n + 1))) : ℝ := if (k : ℕ) % 2 = 0 then -1 else 1

theorem ka_sig_val {n : ℕ} (k : Fin (2 * (n + 1))) :
    ((ka_sig k : Fin (2 * (n + 1))) : ℕ) = if (k : ℕ) % 2 = 0 then (k : ℕ) + 1 else (k : ℕ) - 1 := by
  unfold ka_sig; split_ifs <;> rfl

theorem ka_sig_sig {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sig (ka_sig k) = k := by
  ext
  rw [ka_sig_val, ka_sig_val]
  split_ifs <;> omega

theorem ka_sgn_sig {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sgn (ka_sig k) = - ka_sgn k := by
  unfold ka_sgn
  rw [ka_sig_val]
  split_ifs <;> (try norm_num) <;> omega

theorem ka_sgn_sq {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sgn k * ka_sgn k = 1 := by
  unfold ka_sgn; split_ifs <;> norm_num

def ka_sigE (n : ℕ) : Equiv.Perm (Fin (2 * (n + 1))) :=
  Function.Involutive.toPerm ka_sig ka_sig_sig

theorem ka_sigE_apply {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sigE n k = ka_sig k := rfl

theorem ka_j0_apply {n : ℕ} (v : V n) (k : Fin (2 * (n + 1))) :
    j0 v k = ka_sgn k * v (ka_sig k) := by
  unfold j0 ka_sgn ka_sig
  split_ifs <;> simp

theorem ka_j0_j0 {n : ℕ} (v : V n) : j0 (j0 v) = -v := by
  funext k
  rw [ka_j0_apply, ka_j0_apply, ka_sig_sig, ka_sgn_sig]
  simp only [Pi.neg_apply]
  have := ka_sgn_sq k
  linear_combination (-(v k)) * this

theorem ka_j0_smul {n : ℕ} (a : ℝ) (v : V n) : j0 (a • v) = a • j0 v := by
  funext k; simp only [ka_j0_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem ka_j0_add {n : ℕ} (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [ka_j0_apply, Pi.add_apply]; ring

theorem ka_j0_sub {n : ℕ} (u v : V n) : j0 (u - v) = j0 u - j0 v := by
  funext k; simp only [ka_j0_apply, Pi.sub_apply]; ring

theorem ka_dot_comm {n : ℕ} (u v : V n) : dot u v = dot v u := by
  unfold dot; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem ka_dot_smul_right {n : ℕ} (a : ℝ) (u v : V n) : dot u (a • v) = a * dot u v := by
  unfold dot; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_smul_left {n : ℕ} (a : ℝ) (u v : V n) : dot (a • u) v = a * dot u v := by
  rw [ka_dot_comm, ka_dot_smul_right, ka_dot_comm]

theorem ka_dot_add_right {n : ℕ} (u v w : V n) : dot u (v + w) = dot u v + dot u w := by
  unfold dot; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_add_left {n : ℕ} (u v w : V n) : dot (v + w) u = dot v u + dot w u := by
  rw [ka_dot_comm, ka_dot_add_right, ka_dot_comm, ka_dot_comm u]

theorem ka_dot_sub_right {n : ℕ} (u v w : V n) : dot u (v - w) = dot u v - dot u w := by
  unfold dot; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_sub_left {n : ℕ} (u v w : V n) : dot (v - w) u = dot v u - dot w u := by
  rw [ka_dot_comm, ka_dot_sub_right, ka_dot_comm, ka_dot_comm u]

theorem ka_dot_neg_right {n : ℕ} (u v : V n) : dot u (-v) = - dot u v := by
  unfold dot; rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp)

theorem ka_dot_neg_left {n : ℕ} (u v : V n) : dot (-u) v = - dot u v := by
  rw [ka_dot_comm, ka_dot_neg_right, ka_dot_comm]

theorem ka_dot_j0_left {n : ℕ} (u v : V n) : dot (j0 u) v = - dot u (j0 v) := by
  unfold dot
  rw [← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp (ka_sigE n)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [ka_sigE_apply, ka_j0_apply, ka_sig_sig, ka_sgn_sig]
  ring

theorem ka_dot_j0_j0 {n : ℕ} (u v : V n) : dot (j0 u) (j0 v) = dot u v := by
  rw [ka_dot_j0_left, ka_j0_j0, ka_dot_neg_right, neg_neg]

theorem ka_dot_self_j0 {n : ℕ} (u : V n) : dot u (j0 u) = 0 := by
  have := ka_dot_j0_left u u
  rw [ka_dot_comm] at this
  linarith

theorem ka_clm_apply {n : ℕ} (L : V n →L[ℝ] ℝ) (v : V n) :
    L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show (Pi.single k (v k) : V n) = v k • Pi.single k 1 by
    rw [← Pi.single_smul]; simp]
  rw [map_smul, smul_eq_mul]

theorem ka_fderiv_eq_dot {n : ℕ} (H : V n → ℝ) (x v : V n) :
    fderiv ℝ H x v = dot (grad H x) v := by
  rw [ka_clm_apply]; unfold dot grad
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem ka_liouville_ham {n : ℕ} (H : V n → ℝ) (x : V n) :
    liouville x (hamVF H x) = fderiv ℝ H x x / 2 := by
  unfold liouville omega0 hamVF
  rw [ka_dot_j0_j0, ka_fderiv_eq_dot, ka_dot_comm]

theorem ka_reeb_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) :
    0 < liouville x (hamVF H x) ∧ liouville x (reeb H x) = 1 ∧ fderiv ℝ H x (reeb H x) = 0 ∧
      ∀ w : V n, fderiv ℝ H x w = 0 → omega0 (reeb H x) w = 0 := by
  have hpos : 0 < liouville x (hamVF H x) := by
    rw [ka_liouville_ham]; have := hH.2.2 x hx; linarith
  refine ⟨hpos, ?_, ?_, ?_⟩
  · unfold reeb
    have : liouville x ((liouville x (hamVF H x))⁻¹ • hamVF H x) =
        (liouville x (hamVF H x))⁻¹ * liouville x (hamVF H x) := by
      unfold liouville omega0; rw [ka_dot_smul_right]; ring
    rw [this, inv_mul_cancel₀ hpos.ne']
  · unfold reeb hamVF
    rw [map_smul, ka_fderiv_eq_dot, ka_dot_self_j0, smul_zero]
  · intro w hw
    unfold reeb hamVF omega0
    rw [ka_j0_smul, ka_j0_j0, ka_dot_smul_left, ka_dot_neg_left,
      ← ka_fderiv_eq_dot, hw]; ring

theorem ka_om_add_left {n : ℕ} (u v w : V n) : omega0 (u + v) w = omega0 u w + omega0 v w := by
  unfold omega0; rw [ka_j0_add, ka_dot_add_left]
theorem ka_om_add_right {n : ℕ} (u v w : V n) : omega0 w (u + v) = omega0 w u + omega0 w v := by
  unfold omega0; rw [ka_dot_add_right]
theorem ka_om_sub_left {n : ℕ} (u v w : V n) : omega0 (u - v) w = omega0 u w - omega0 v w := by
  unfold omega0; rw [ka_j0_sub, ka_dot_sub_left]
theorem ka_om_sub_right {n : ℕ} (u v w : V n) : omega0 w (u - v) = omega0 w u - omega0 w v := by
  unfold omega0; rw [ka_dot_sub_right]
theorem ka_om_smul_left {n : ℕ} (a : ℝ) (u w : V n) : omega0 (a • u) w = a * omega0 u w := by
  unfold omega0; rw [ka_j0_smul, ka_dot_smul_left]
theorem ka_om_smul_right {n : ℕ} (a : ℝ) (u w : V n) : omega0 w (a • u) = a * omega0 w u := by
  unfold omega0; rw [ka_dot_smul_right]
theorem ka_om_anti {n : ℕ} (u v : V n) : omega0 u v = - omega0 v u := by
  unfold omega0; rw [ka_dot_j0_left, ka_dot_comm]
theorem ka_om_self {n : ℕ} (u : V n) : omega0 u u = 0 := by
  have := ka_om_anti u u; linarith

theorem ka_liouvilleCLM_apply {n : ℕ} (x v : V n) : liouvilleCLM x v = liouville x v := by
  unfold liouvilleCLM liouville omega0 dot
  simp [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)

theorem ka_scale_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : 0 < scaleToS H y ∧ H (scaleToS H y • y) = 1 := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
  unfold scaleToS
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem ka_scale_unique {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) (t : ℝ) (ht : 0 < t) (hHt : H (t • y) = 1) : scaleToS H y = t := by
  obtain ⟨r, _, hu⟩ := hH.2.1 y hy
  have h1 := hu t ⟨ht, hHt⟩
  have h2 := hu (scaleToS H y) (ka_scale_spec H hH y hy)
  rw [h1, h2]

theorem ka_scale_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y₀ : V n)
    (hy₀ : y₀ ≠ 0) : ContDiffAt ℝ ∞ (scaleToS H) y₀ := by
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y₀ hy₀
  set r := scaleToS H y₀
  set f : V n × ℝ → ℝ := fun p => H (p.2 • p.1) with hf
  have hfc : ContDiff ℝ ∞ f := hH.1.comp (ContDiff.smul contDiff_snd contDiff_fst)
  set u : V n × ℝ := (y₀, r)
  have cdf : ContDiffAt ℝ ∞ f u := hfc.contDiffAt
  have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  -- derivative
  have hg : HasFDerivAt (fun p : V n × ℝ => p.2 • p.1)
      (r • ContinuousLinearMap.fst ℝ (V n) ℝ + (ContinuousLinearMap.snd ℝ (V n) ℝ).smulRight y₀) u := by
    have h1 : HasFDerivAt (fun p : V n × ℝ => p.2) (ContinuousLinearMap.snd ℝ (V n) ℝ) u :=
      hasFDerivAt_snd
    have h2 : HasFDerivAt (fun p : V n × ℝ => p.1) (ContinuousLinearMap.fst ℝ (V n) ℝ) u :=
      hasFDerivAt_fst
    exact h1.smul h2
  have hHd : HasFDerivAt H (fderiv ℝ H (r • y₀)) (r • y₀) :=
    (hH.1.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hfd : HasFDerivAt f ((fderiv ℝ H (r • y₀)).comp
      (r • ContinuousLinearMap.fst ℝ (V n) ℝ + (ContinuousLinearMap.snd ℝ (V n) ℝ).smulRight y₀)) u :=
    hHd.comp u hg
  have hpos : 0 < fderiv ℝ H (r • y₀) y₀ := by
    have := hH.2.2 (r • y₀) hHx
    rw [map_smul, smul_eq_mul] at this
    exact pos_of_mul_pos_right this hr.le
  set c := fderiv ℝ H (r • y₀) y₀
  have hL1 : (fderiv ℝ f u ∘L .inr ℝ (V n) ℝ) 1 = c := by
    rw [hfd.fderiv]; simp [c]
  have if₂ : (fderiv ℝ f u ∘L .inr ℝ (V n) ℝ).IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · apply ContinuousLinearMap.ext_ring
      rw [ContinuousLinearMap.comp_apply]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
      rw [show c⁻¹ = c⁻¹ • (1:ℝ) by simp, map_smul, hL1, smul_eq_mul, inv_mul_cancel₀ hpos.ne']
    · apply ContinuousLinearMap.ext_ring
      rw [ContinuousLinearMap.comp_apply, hL1]
      simp [inv_mul_cancel₀ hpos.ne']
  set ψ := ContDiffAt.implicitFunction cdf pn if₂
  have hψc : ContDiffAt ℝ ∞ ψ y₀ := ContDiffAt.contDiffAt_implicitFunction cdf pn if₂
  have hψ0 : ψ y₀ = r := ContDiffAt.implicitFunction_apply_self cdf pn if₂
  have hψeq := ContDiffAt.eventually_apply_implicitFunction cdf pn if₂
  have hψpos : ∀ᶠ y in 𝓝 y₀, 0 < ψ y := by
    have := hψc.continuousAt.eventually (lt_mem_nhds (show (0:ℝ) < ψ y₀ by rw [hψ0]; exact hr))
    exact this
  have hne : ∀ᶠ y in 𝓝 y₀, y ≠ 0 := isOpen_ne.mem_nhds hy₀
  have hev : ψ =ᶠ[𝓝 y₀] scaleToS H := by
    filter_upwards [hψeq, hψpos, hne] with y h1 h2 h3
    have h1' : H (ψ y • y) = 1 := by
      have : f (y, ψ y) = f u := h1
      simp only [hf, u] at this
      rw [this, hHx]
    exact (ka_scale_unique H hH y h3 (ψ y) h2 h1').symm
  exact hψc.congr_of_eventuallyEq hev.symm


theorem ka_j0_contDiff {n : ℕ} : ContDiff ℝ ∞ (j0 : V n → V n) := by
  refine contDiff_pi.2 (fun k => ?_)
  have : (fun v : V n => j0 v k) = fun v => ka_sgn k * v (ka_sig k) := by
    funext v; exact ka_j0_apply v k
  rw [this]
  exact contDiff_const.mul (contDiff_apply ℝ ℝ (ka_sig k))

theorem ka_dH_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (m := ∞) (by simp)

theorem ka_grad_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (grad H) := by
  refine contDiff_pi.2 (fun k => ?_)
  exact (ka_dH_contDiff H hH).clm_apply contDiff_const

theorem ka_hamVF_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (hamVF H) := ka_j0_contDiff.comp (ka_grad_contDiff H hH)

theorem ka_liouvilleCLM_contDiff {n : ℕ} : ContDiff ℝ ∞ (liouvilleCLM : V n → V n →L[ℝ] ℝ) := by
  unfold liouvilleCLM
  refine ContDiff.const_smul _ (ContDiff.sum (fun k _ => ?_))
  exact ((contDiff_apply ℝ ℝ k).comp ka_j0_contDiff).smul contDiff_const

theorem ka_reeb_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) : ContDiffAt ℝ ∞ (reeb H) x := by
  have hpos := (ka_reeb_spec H hH x hx).1
  have hL : (fun x => liouville x (hamVF H x)) = fun x => liouvilleCLM x (hamVF H x) := by
    funext x; rw [ka_liouvilleCLM_apply]
  have hc : ContDiff ℝ ∞ (fun x => liouville x (hamVF H x)) := by
    rw [hL]; exact ka_liouvilleCLM_contDiff.clm_apply (ka_hamVF_contDiff H hH.1)
  unfold reeb
  exact (hc.contDiffAt.inv hpos.ne').smul (ka_hamVF_contDiff H hH.1).contDiffAt

theorem ka_scale_hasFDerivAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) :
    HasFDerivAt (scaleToS H)
      ((-(scaleToS H y ^ 2 / fderiv ℝ H (proj H y) (proj H y))) • fderiv ℝ H (proj H y)) y := by
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y hy
  have hd : DifferentiableAt ℝ (scaleToS H) y :=
    (ka_scale_contDiffAt H hH y hy).differentiableAt (by simp)
  set r := scaleToS H y
  set x := proj H y
  have hxr : x = r • y := rfl
  set L := fderiv ℝ (scaleToS H) y
  have hm : HasFDerivAt (fun y' => scaleToS H y' • y') (r • ContinuousLinearMap.id ℝ (V n) +
      L.smulRight y) y := hd.hasFDerivAt.smul (hasFDerivAt_id y)
  have hHd : HasFDerivAt H (fderiv ℝ H x) x :=
    (hH.1.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hg := hHd.comp y hm
  have hev : (H ∘ fun y' => scaleToS H y' • y') =ᶠ[𝓝 y] fun _ => (1:ℝ) := by
    filter_upwards [isOpen_ne.mem_nhds hy] with y' hy'
    exact (ka_scale_spec H hH y' hy').2
  have h0 := hg.fderiv
  rw [hev.fderiv_eq, fderiv_fun_const] at h0
  have hD : 0 < fderiv ℝ H x x := hH.2.2 x hHx
  have hL : ∀ v, L v = -(r ^ 2 / fderiv ℝ H x x) * fderiv ℝ H x v := by
    intro v
    have := congrArg (fun T => T v) h0
    simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
      smul_eq_mul] at this
    have hxy : fderiv ℝ H x y = fderiv ℝ H x x / r := by
      rw [hxr, map_smul, smul_eq_mul]; field_simp
    rw [hxy] at this
    field_simp
    field_simp at this
    linarith
  have : L = (-(r ^ 2 / fderiv ℝ H x x)) • fderiv ℝ H x := by
    ext1 v; rw [hL v]; rfl
  rw [← this]; exact hd.hasFDerivAt

theorem ka_hol_abstract {n : ℕ} (A B : V n) (P : V n → Prop) (J' : V n →L[ℝ] V n)
    (α β : V n →L[ℝ] ℝ)
    (hW : ∀ v, P (v - α v • A - β v • B)) (hJP : ∀ w, P w → P (J' w))
    (hαA : α A = 1) (hαB : α B = 0) (hβA : β A = 0) (hβB : β B = 1)
    (hαP : ∀ w, P w → α w = 0) (hβP : ∀ w, P w → β w = 0)
    (hB : ∀ w, P w → omega0 B w = 0) (us ut : V n)
    (hhol : us + (α ut • B - β ut • A + J' (ut - α ut • A - β ut • B)) = 0) :
    α us = β ut ∧ α ut = - β us ∧
      omega0 (us - α us • A) (ut - α ut • A) =
        omega0 (ut - α ut • A - β ut • B) (J' (ut - α ut • A - β ut • B)) ∧
      (β us = 0 → β ut = 0 → ut - α ut • A - β ut • B = 0 → us = 0 ∧ ut = 0) := by
  set w := ut - α ut • A - β ut • B with hwdef
  have hPw : P w := hW ut
  have hPJw := hJP _ hPw
  have hs : us = -(α ut • B - β ut • A + J' w) := eq_neg_of_add_eq_zero_left hhol
  have e1 : α us = β ut := by
    rw [hs, map_neg, map_add, hαP _ hPJw]
    simp only [map_sub, map_smul, hαA, hαB, smul_eq_mul]; ring
  have e2 : β us = - α ut := by
    rw [hs, map_neg, map_add, hβP _ hPJw]
    simp only [map_sub, map_smul, hβA, hβB, smul_eq_mul]; ring
  have hus : us - α us • A = β us • B - J' w := by
    rw [e1, e2]; rw [hs]; module
  have hut : ut - α ut • A = β ut • B + w := by rw [hwdef]; module
  have hBB : omega0 B B = 0 := ka_om_self B
  have hJwB : omega0 (J' w) B = 0 := by rw [ka_om_anti, hB _ hPJw, neg_zero]
  refine ⟨e1, by linarith, ?_, ?_⟩
  · rw [hus, hut]
    simp only [ka_om_add_right, ka_om_sub_left, ka_om_smul_left, ka_om_smul_right,
      hBB, hB _ hPw, hJwB]
    rw [ka_om_anti (J' w) w]; ring
  · intro h1 h2 h3
    have hw0 : w = 0 := h3
    have hα : α ut = 0 := by linarith
    have hJ0 : J' w = 0 := by rw [hw0, map_zero]
    constructor
    · rw [hs, hJ0, h2, hα]; simp
    · have : ut = α ut • A + β ut • B + w := by rw [hwdef]; module
      rw [this, hα, h2, hw0]; simp

theorem ka_clm_complex_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℂ →L[ℝ] E) (h1 : L 1 = 0) (hI : L Complex.I = 0) : L = 0 := by
  ext1 z
  have : z = z.re • (1:ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [this, map_add, map_smul, map_smul, h1, hI]; simp

theorem ka_cr {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (z : ℂ)
    (hdu : DifferentiableAt ℝ u z) (hz : u z ≠ 0)
    (hhol : JHolomorphic.dbarJ (Jtilde H J) u z = 0) :
    ds (fun z => aCoord H (u z)) z = liouville (proj H (u z)) (dt (fun z => proj H (u z)) z) ∧
    dt (fun z => aCoord H (u z)) z = -liouville (proj H (u z)) (ds (fun z => proj H (u z)) z) := by
  set y := u z with hydef
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y hz
  set r := scaleToS H y with hrdef
  set x := proj H y with hxdef
  have hxr : x = r • y := rfl
  have hx : x ∈ energySurface H := hHx
  have hyx : y = r⁻¹ • x := by rw [hxr, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  obtain ⟨hc, hR1, hRH, hRw⟩ := ka_reeb_spec H hH x hx
  set R := reeb H x
  set D := fderiv ℝ H x x
  have hD : 0 < D := hH.2.2 x hx
  set α : V n →L[ℝ] ℝ := (r / (2 * D)) • fderiv ℝ H x with hαdef
  set β : V n →L[ℝ] ℝ := r • liouvilleCLM x with hβdef
  set A : V n := (2:ℝ) • y
  set B : V n := r⁻¹ • R
  have hLA : liouvilleCLM x A = 0 := by
    simp only [A, hyx, ka_liouvilleCLM_apply]
    unfold liouville; simp only [ka_om_smul_right, ka_om_self]; ring
  -- derivatives
  have hS' := ka_scale_hasFDerivAt H hH y hz
  have ha' : HasFDerivAt (aCoord H) α y := by
    have h1 := (hS'.log hr.ne').const_mul (-1/2 : ℝ)
    have : (fun y => (-1/2 : ℝ) * Real.log (scaleToS H y)) = aCoord H := by
      funext y; unfold aCoord; ring
    rw [this] at h1
    have heq : α = ((-1 / 2 : ℝ) • (scaleToS H y)⁻¹ • -(scaleToS H y ^ 2 /
        (fderiv ℝ H (proj H y)) (proj H y)) • fderiv ℝ H (proj H y)) := by
      ext1 v
      simp only [hαdef, ContinuousLinearMap.smul_apply, smul_eq_mul, ← hrdef, ← hxdef]
      have hD' : fderiv ℝ H x x ≠ 0 := hD.ne'
      field_simp
      exact mul_comm _ _
    rw [heq]; exact h1
  have hp' : HasFDerivAt (proj H) (r • (ContinuousLinearMap.id ℝ (V n) - α.smulRight A)) y := by
    have h1 := hS'.smul (hasFDerivAt_id y)
    have heq : r • (ContinuousLinearMap.id ℝ (V n) - α.smulRight A) =
        scaleToS H y • ContinuousLinearMap.id ℝ (V n) +
        ((-(scaleToS H y ^ 2 / fderiv ℝ H (proj H y) (proj H y))) • fderiv ℝ H (proj H y)).smulRight y := by
      ext1 v
      simp only [hαdef, A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, smul_eq_mul, ← hrdef, ← hxdef, smul_sub, smul_smul]
      have hD' : fderiv ℝ H x x ≠ 0 := hD.ne'
      rw [sub_eq_add_neg, ← neg_smul]
      congr 2
      field_simp
      ring
    rw [heq]; exact h1
  set us := fderiv ℝ u z 1
  set ut := fderiv ℝ u z Complex.I
  have hdsa : ds (fun z => aCoord H (u z)) z = α us := by
    unfold ds; rw [show (fun z => aCoord H (u z)) = aCoord H ∘ u from rfl, (ha'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdta : dt (fun z => aCoord H (u z)) z = α ut := by
    unfold dt; rw [show (fun z => aCoord H (u z)) = aCoord H ∘ u from rfl, (ha'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdsw : ds (fun z => proj H (u z)) z = r • (us - α us • A) := by
    unfold ds; rw [show (fun z => proj H (u z)) = proj H ∘ u from rfl, (hp'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdtw : dt (fun z => proj H (u z)) z = r • (ut - α ut • A) := by
    unfold dt; rw [show (fun z => proj H (u z)) = proj H ∘ u from rfl, (hp'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hWgen : ∀ v, IsInXi H x (v - α v • A - β v • B) := by
    intro v
    simp only [hαdef, hβdef, ContinuousLinearMap.smul_apply, ka_liouvilleCLM_apply, smul_eq_mul]
    constructor
    · unfold liouville
      rw [ka_om_sub_right, ka_om_sub_right]
      simp only [A, B, hyx, ka_om_smul_right]
      have h1 : omega0 x x = 0 := ka_om_self x
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h1, h2]; field_simp; ring
    · simp only [A, B, map_sub, map_smul, smul_eq_mul, hRH, hyx]
      field_simp; ring
  have key := ka_hol_abstract A B (IsInXi H x) (J x) α β hWgen
    (fun w hw => (hJ.2 x hx w w hw hw).1)
    (by
      simp only [hαdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hyx]
      field_simp
      rfl)
    (by simp only [hαdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hRH]; ring)
    (by
      simp only [hβdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply, hyx]
      unfold liouville; simp only [ka_om_smul_right, ka_om_self]; ring)
    (by
      simp only [hβdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply]
      unfold liouville; simp only [ka_om_smul_right]
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h2]; field_simp)
    (fun w hw => by
      simp only [hαdef, ContinuousLinearMap.smul_apply, smul_eq_mul, hw.2]; ring)
    (fun w hw => by
      simp only [hβdef, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply, hw.1]; ring)
    (fun w hw => by simp only [B]; rw [ka_om_smul_left, hRw w hw.2]; ring)
    us ut hhol
  obtain ⟨e1, e2, e3, e4⟩ := key
  set W := ut - α ut • A - β ut • B
  have hPW : IsInXi H x W := hWgen ut
  have hm : 0 ≤ omega0 W (J x W) := by
    by_cases h0 : W = 0
    · rw [h0, map_zero, ka_om_self]
    · exact ((hJ.2 x hx W W hPW hPW).2.2.1 h0).le
  have hLs : liouville x (r • (us - α us • A)) = β us := by
    rw [← ka_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  have hLt : liouville x (r • (ut - α ut • A)) = β ut := by
    rw [← ka_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  refine ⟨?_, ?_⟩
  · rw [hdsa, hdtw, hLt, e1]
  · rw [hdta, hdsw, hLs, e2]



namespace KAo
open FiniteEnergyPlane
variable {n : ℕ}

/-- `j0` as a continuous linear map. -/
noncomputable def j0L : V n →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := j0, map_add' := ka_j0_add, map_smul' := ka_j0_smul }

/-- `ω₀` as a continuous bilinear map. -/
noncomputable def omegaL : V n →L[ℝ] V n →L[ℝ] ℝ :=
  ∑ k, ((ContinuousLinearMap.proj k).comp j0L).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (n + 1)) => ℝ) k)

theorem omegaL_apply (u v : V n) : omegaL u v = omega0 u v := by
  simp [omegaL, omega0, dot, ContinuousLinearMap.sum_apply, j0L]

end KAo

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

/-- Away from `0`, the symplectization coordinates `aCoord H` and `proj H` are smooth. -/
theorem contDiffAt_aCoord_proj_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (y : V n) (hy : y ≠ 0) : ContDiffAt ℝ ∞ (aCoord H) y ∧ ContDiffAt ℝ ∞ (proj H) y := by
  have hr := (ka_scale_spec H hH y hy).1
  have hd : ContDiffAt ℝ ∞ (scaleToS H) y := ka_scale_contDiffAt H hH y hy
  constructor
  · have : aCoord H = fun y => (-1 / 2 : ℝ) * Real.log (scaleToS H y) := by
      funext y; unfold aCoord; ring
    rw [this]
    exact contDiffAt_const.mul (hd.log hr.ne')
  · have : proj H = fun y => scaleToS H y • y := rfl
    rw [this]
    exact hd.smul contDiffAt_id

theorem emb_exp_aCoord_smul_proj {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (y : V n) (hy : y ≠ 0) : Real.exp (2 * aCoord H y) • proj H y = y := by
  have hr := (ka_scale_spec H hH y hy).1
  have e : Real.exp (2 * aCoord H y) = (scaleToS H y)⁻¹ := by
    unfold aCoord
    rw [show 2 * (-Real.log (scaleToS H y) / 2) = -Real.log (scaleToS H y) by ring,
      Real.exp_neg, Real.exp_log hr]
  rw [e]
  unfold proj
  rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- If `u : E → V n` is differentiable at `z`, `u z ≠ 0`, then the derivative of `u` at `z` is
injective if and only if the derivative at `z` of the symplectization coordinates
`w ↦ (aCoord H (u w), proj H (u w))` is. -/
theorem injective_fderiv_aCoord_proj_comp_iff_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (u : E → V n) (z : E)
    (hu : DifferentiableAt ℝ u z) (h0 : u z ≠ 0) :
    Function.Injective (fderiv ℝ (fun w => (aCoord H (u w), proj H (u w))) z) ↔
      Function.Injective (fderiv ℝ u z) := by
  obtain ⟨ha, hp⟩ := contDiffAt_aCoord_proj_aux H hH (u z) h0
  have hda : DifferentiableAt ℝ (aCoord H) (u z) := ha.differentiableAt (by simp)
  have hdp : DifferentiableAt ℝ (proj H) (u z) := hp.differentiableAt (by simp)
  have hA : HasFDerivAt (fun w => aCoord H (u w)) ((fderiv ℝ (aCoord H) (u z)).comp (fderiv ℝ u z)) z :=
    hda.hasFDerivAt.comp z hu.hasFDerivAt
  have hB : HasFDerivAt (fun w => proj H (u w)) ((fderiv ℝ (proj H) (u z)).comp (fderiv ℝ u z)) z :=
    hdp.hasFDerivAt.comp z hu.hasFDerivAt
  have hG := hA.prodMk hB
  rw [hG.fderiv]
  -- the formula expressing `u` through its coordinates
  have hev : (fun w => Real.exp (2 * aCoord H (u w)) • proj H (u w)) =ᶠ[𝓝 z] u := by
    filter_upwards [hu.continuousAt.eventually_ne h0] with w hw
    exact emb_exp_aCoord_smul_proj H hH (u w) hw
  have hexp := (hA.const_mul 2).exp
  have hsm := (hexp.smul hB).congr_of_eventuallyEq hev.symm
  have hdu := hsm.unique hu.hasFDerivAt
  constructor
  · intro hinj
    rw [injective_iff_map_eq_zero]
    intro v hv
    apply (injective_iff_map_eq_zero _).1 hinj
    simp [hv]
  · intro hinj
    rw [injective_iff_map_eq_zero]
    intro v hv
    apply (injective_iff_map_eq_zero _).1 hinj
    have hv1 : ((fderiv ℝ (aCoord H) (u z)).comp (fderiv ℝ u z)) v = 0 := congrArg Prod.fst hv
    have hv2 : ((fderiv ℝ (proj H) (u z)).comp (fderiv ℝ u z)) v = 0 := congrArg Prod.snd hv
    rw [← hdu]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply']
    simp [hv1, hv2]

end FiniteEnergyPlane

/-! Child A of Hryniewicz Lemma 6.24: the `S`-component of an embedded fast plane is injective. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem injective_proj_of_isEmbeddedPlane_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hue : IsEmbeddedPlane u) :
    Function.Injective (fun z => proj H (u z)) := by
  have hfu := hu.1
  have hsu : ContDiff ℝ ∞ u := contDiffOn_univ.1 hfu.1
  have hu0 : ∀ z, u z ≠ 0 := fun z => hfu.2.1 z trivial
  have hcu : Continuous u := hsu.continuous
  have hui : ∀ z, Function.Injective (fderiv ℝ u z) := hue.2
  have hsh : ∀ c, IsFiniteEnergyCurve H J Set.univ (shiftA c u) := fun c =>
    (isFastPlane_shiftA H hH J hJ u hu c).1
  have hshi : ∀ c w, Function.Injective (fderiv ℝ (shiftA c u) w) := fun c w =>
    moh_fderiv_shiftA_inj u hsu c w (hui w)
  -- local injectivity of `proj ∘ u`
  have hpd : ∀ z, ContDiffAt ℝ ∞ (fun z => proj H (u z)) z := fun z =>
    ((contDiffAt_aCoord_proj H hH (u z) (hu0 z)).2).comp z hsu.contDiffAt
  have hloc : ∀ a : ℂ, ∃ ε > 0, Set.InjOn (fun z => proj H (u z)) (ball a ε) := by
    intro a
    refine moh_locInj _ a ((hpd a).of_le (by simp)) ?_
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    exact isFastPlane_immersion_transverse H hH J hJ u hu a v hv0 0 (by rw [hv, zero_smul])
  obtain hFB := exists_forall_norm_lt_of_eq_shiftA_self H hH J hJ P u hu huP
  set A : ℝ → Set (ℂ × ℂ) := fun τ => {p : ℂ × ℂ | u p.1 = shiftA τ u p.2} with hA
  have hAcl : ∀ τ, IsClosed (A τ) := fun τ =>
    isClosed_eq (hcu.comp continuous_fst) ((hcu.const_smul (Real.exp (2 * τ))).comp continuous_snd)
  have main : ∀ τ₁ > 0, ∀ z w : ℂ, u z ≠ shiftA τ₁ u w := by
    intro τ₁ hτ₁ z₁ w₁ h₁
    obtain ⟨R, hR⟩ := hFB τ₁
    set KK : Set (ℂ × ℂ) := closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R with hKK
    have hKc : IsCompact KK := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
    have hAK : ∀ τ, 0 < τ → τ ≤ τ₁ → A τ ⊆ KK := by
      intro τ hτ hτ' p hp
      have h := hR τ p.1 p.2 hp hτ.ne' (by rw [abs_of_pos hτ]; exact hτ')
      exact ⟨mem_closedBall_zero_iff.2 h.1.le, mem_closedBall_zero_iff.2 h.2.le⟩
    set S : Set ℝ := {τ : ℝ | 0 < τ ∧ τ ≤ τ₁ ∧ (A τ).Nonempty} with hS
    have hτ₁S : τ₁ ∈ S := ⟨hτ₁, le_rfl, (z₁, w₁), h₁⟩
    have hbdd : BddBelow S := ⟨0, fun τ hτ => hτ.1.le⟩
    obtain ⟨t, -, ht, htS⟩ := exists_seq_tendsto_sInf ⟨τ₁, hτ₁S⟩ hbdd
    set σ := sInf S with hσ
    have hσ0 : 0 ≤ σ := le_csInf ⟨τ₁, hτ₁S⟩ (fun b hb => hb.1.le)
    have hστ : σ ≤ τ₁ := csInf_le hbdd hτ₁S
    choose q hq using fun n => (htS n).2.2
    have hqK : ∀ n, q n ∈ KK := fun n => hAK (t n) (htS n).1 (htS n).2.1 (hq n)
    obtain ⟨p, -, φ, hφ, hlim⟩ := hKc.tendsto_subseq hqK
    have hpA : p ∈ A σ := by
      have h1 : Tendsto (fun n => u (q (φ n)).1) atTop (𝓝 (u p.1)) :=
        (hcu.tendsto _).comp ((continuous_fst.tendsto _).comp hlim)
      have h2 : Tendsto (fun n => Real.exp (2 * t (φ n)) • u (q (φ n)).2) atTop
          (𝓝 (Real.exp (2 * σ) • u p.2)) :=
        ((Real.continuous_exp.tendsto _).comp
          (tendsto_const_nhds.mul (ht.comp hφ.tendsto_atTop))).smul
          ((hcu.tendsto _).comp ((continuous_snd.tendsto _).comp hlim))
      exact tendsto_nhds_unique h1 (Tendsto.congr (fun n => (hq (φ n)).symm) h2)
    rcases hσ0.lt_or_eq with hσpos | hσz
    · -- `σ > 0`: persistence gives intersections just below `σ`
      have hset : {r : ℂ × ℂ | r ∈ (Set.univ : Set (ℂ × ℂ)) ∧ u r.1 = shiftA σ u r.2} = A σ := by
        ext r; simp [hA]
      have hiso := forall_isolated_of_isBounded_of_isClosed H hH J hJ u (shiftA σ u) hfu (hsh σ)
        hui (hshi σ) Set.univ isOpen_univ (hset ▸ hAcl σ)
        (hset ▸ hKc.isBounded.subset (hAK σ hσpos hστ)) p trivial hpA
      have hcu' : JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => shiftA 0 u) (shiftA 0 u)
          Set.univ :=
        tendstoCInftyLocOn_shiftA u hsu (fun _ => 0) 0 tendsto_const_nhds Set.univ
      rw [moh_shiftA_zero] at hcu'
      set c : ℕ → ℝ := fun k => σ - σ / ((k : ℝ) + 2) with hc
      have hcl : Tendsto c atTop (𝓝 σ) := by
        have h0 : Tendsto (fun k : ℕ => σ / ((k : ℝ) + 2)) atTop (𝓝 0) := by
          have := tendsto_atTop_add_const_right atTop (2 : ℝ)
            (tendsto_natCast_atTop_atTop (R := ℝ))
          exact tendsto_const_nhds.div_atTop this
        have := (tendsto_const_nhds (x := σ)).sub h0
        rw [sub_zero] at this; exact this
      have hcv' := tendstoCInftyLocOn_shiftA u hsu c σ hcl Set.univ
      obtain ⟨z, w, -, -, hev⟩ := exists_intersection_of_tendstoCInftyLocOn H hH J hJ Set.univ
        Set.univ isOpen_univ isOpen_univ u (shiftA σ u) (fun _ => u) (fun k => shiftA (c k) u)
        hfu (hsh σ) (fun z _ => hui z) (fun w _ => hshi σ w) (fun _ => hfu) (fun k => hsh (c k))
        hcu' hcv' p.1 p.2 trivial trivial hpA hiso
      obtain ⟨k, hk⟩ := hev.exists
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have hlt : σ / ((k : ℝ) + 2) < σ := by
        rw [div_lt_iff₀ hk2]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have hpos : 0 < σ / ((k : ℝ) + 2) := div_pos hσpos hk2
      have hkS : c k ∈ S := ⟨by simp only [hc]; linarith, by simp only [hc]; linarith,
        (z k, w k), hk⟩
      have := csInf_le hbdd hkS
      simp only [hc] at this
      linarith
    · -- `σ = 0`: the limit is a diagonal point, where `proj ∘ u` is locally injective
      rw [← hσz] at hpA
      have hp : u p.1 = u p.2 := by
        have : u p.1 = shiftA 0 u p.2 := hpA
        rwa [moh_shiftA_zero] at this
      have hpp : p.1 = p.2 := hue.1 hp
      obtain ⟨ε, hε, hinj⟩ := hloc p.1
      have hmem : ∀ᶠ n in atTop, q (φ n) ∈ ball p.1 ε ×ˢ ball p.1 ε := by
        have hO : ball p.1 ε ×ˢ ball p.1 ε ∈ 𝓝 p := by
          rw [show p = (p.1, p.2) from rfl, ← hpp]
          exact prod_mem_nhds (ball_mem_nhds _ hε) (ball_mem_nhds _ hε)
        exact hlim hO
      obtain ⟨n, hn⟩ := hmem.exists
      have hrel := moh_shift_rel H hH u hu0 (t (φ n)) _ _ (hq (φ n))
      have heq : (q (φ n)).1 = (q (φ n)).2 := hinj hn.1 hn.2 hrel.1
      have h3 : u (q (φ n)).2 = shiftA (t (φ n)) u (q (φ n)).2 := by
        have h4 : u (q (φ n)).1 = shiftA (t (φ n)) u (q (φ n)).2 := hq (φ n)
        rwa [heq] at h4
      exact (htS (φ n)).1.ne' (moh_tau_eq_zero u hu0 _ _ h3)
  intro z w hzw
  simp only at hzw
  by_contra hne
  have ez := emb_exp_aCoord_smul_proj H hH (u z) (hu0 z)
  have ew := emb_exp_aCoord_smul_proj H hH (u w) (hu0 w)
  set τ := aCoord H (u z) - aCoord H (u w) with hτ
  have hrel : u z = shiftA τ u w := by
    show u z = Real.exp (2 * τ) • u w
    conv_rhs => rw [← ew, smul_smul, ← Real.exp_add, ← hzw]
    rw [show 2 * τ + 2 * aCoord H (u w) = 2 * aCoord H (u z) by rw [hτ]; ring]
    exact ez.symm
  rcases lt_trichotomy τ 0 with hneg | hzero | hpos
  · exact main (-τ) (by linarith) w z (moh_shift_symm u τ z w hrel)
  · rw [hzero, moh_shiftA_zero] at hrel
    exact hne (hue.1 hrel)
  · exact main τ hpos z w hrel

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hue : IsEmbeddedPlane u) :
    Function.Injective (fun z => proj H (u z)) :=
  FiniteEnergyPlane.injective_proj_of_isEmbeddedPlane_aux H hH J hJ P u hu huP hue
