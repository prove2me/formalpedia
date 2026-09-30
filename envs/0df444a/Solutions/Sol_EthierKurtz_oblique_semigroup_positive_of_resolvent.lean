-- Prove2me | solution 1 for EthierKurtz.oblique_semigroup_positive_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T00:37:32.300458+00:00
-- url     : https://prove2.me/submissions/66f69476-76ca-4900-ad28-3be96a253fd3

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace EK376

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {T : ℝ → E →L[ℝ] E}

theorem T_norm_le (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T)
    {t : ℝ} (ht : 0 ≤ t) (x : E) : ‖T t x‖ ≤ ‖x‖ :=
  (T t).le_opNorm x |>.trans (by
    have := hT.2.2.1 t ht
    nlinarith [norm_nonneg x])

theorem T_comm (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : E) : T s (T t x) = T t (T s x) := by
  have h1 := hT.2.1 s t hs ht
  have h2 := hT.2.1 t s ht hs
  rw [add_comm] at h2
  have := h1.symm.trans h2
  exact congrArg (fun L => L x) this

theorem T_shift (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (x : E) : T a (T (b - a) x) = T b x := by
  have := hT.2.1 a (b - a) ha (by linarith)
  rw [show a + (b - a) = b by ring] at this
  rw [this, ContinuousLinearMap.comp_apply]

theorem T_cont (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T) (x : E) :
    ContinuousOn (fun s => T s x) (Ici 0) := by
  intro s hs
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.tendsto_nhdsWithin_nhds.1 (hT.2.2.2 x) ε hε
  refine ⟨δ, hδ, fun {s'} hs' hd => ?_⟩
  have key : ∀ a b : ℝ, 0 ≤ a → a < b → b - a < δ → ‖T b x - T a x‖ < ε := by
    intro a b ha hab hba
    have h1 : T b x - T a x = T a (T (b - a) x - x) := by
      rw [map_sub, T_shift hT ha hab.le]
    rw [h1]
    refine lt_of_le_of_lt (T_norm_le hT ha _) ?_
    have := hδ' (show (0:ℝ) < b - a by linarith)
      (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; exact hba)
    rwa [dist_eq_norm] at this
  have hs0 : (0:ℝ) ≤ s := hs
  have hs0' : (0:ℝ) ≤ s' := hs'
  rw [Real.dist_eq] at hd
  rw [dist_eq_norm]
  rcases lt_trichotomy s s' with h | h | h
  · exact key s s' hs0 h (by rw [abs_lt] at hd; linarith)
  · subst h; simpa using hε
  · rw [norm_sub_rev]; exact key s' s hs0' h (by rw [abs_lt] at hd; linarith)

/-- The generator relation. -/
def Gen (T : ℝ → E →L[ℝ] E) (f g : E) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[>] (0 : ℝ)) (𝓝 g)

theorem Gen_sub {f g f' g' : E} (h : Gen T f g) (h' : Gen T f' g') :
    Gen T (f - f') (g - g') := by
  unfold Gen at *
  refine (h.sub h').congr (fun t => ?_)
  rw [map_sub, ← smul_sub]
  congr 1
  abel

theorem Gen_smul (c : ℝ) {f g : E} (h : Gen T f g) : Gen T (c • f) (c • g) := by
  unfold Gen at *
  refine (h.const_smul c).congr (fun t => ?_)
  rw [map_smul, ← smul_sub, smul_comm]

theorem T_hasDerivWithinAt (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T)
    {z w : E} (hz : Gen T z w) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (fun r => T r z) (T s w) (Ici s) s := by
  rw [← hasDerivWithinAt_Ioi_iff_Ici,
    hasDerivWithinAt_iff_tendsto_slope' (show s ∉ Ioi s from lt_irrefl s)]
  have h1 : Tendsto (fun y : ℝ => y - s) (𝓝[>] s) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun y : ℝ => y - s) (𝓝 s) (𝓝 (s - s)) :=
        ((continuous_id.sub continuous_const).tendsto s)
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact sub_pos.2 (mem_Ioi.1 hy)
  have h2 := ((T s).continuous.tendsto w).comp (hz.comp h1)
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : s < y := hy
  simp only [Function.comp_apply]
  rw [slope_def_module, map_smul, map_sub, T_shift hT hs hy'.le]

end Basic

section Res

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : ℝ → E →L[ℝ] E}

noncomputable def G (T : ℝ → E →L[ℝ] E) (lam : ℝ) (x : E) (s : ℝ) : E :=
  Real.exp (-lam * s) • T (max s 0) x

theorem G_cont (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T) (lam : ℝ) (x : E) :
    Continuous (G T lam x) := by
  unfold G
  refine (Real.continuous_exp.comp (by fun_prop)).smul ?_
  exact (T_cont hT x).comp_continuous (continuous_id.max continuous_const)
    (fun s => Set.mem_Ici.2 (le_max_right s 0))

theorem G_norm (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T) (lam : ℝ) (x : E)
    {s : ℝ} (hs : 0 ≤ s) : ‖G T lam x s‖ ≤ Real.exp (-lam * s) * ‖x‖ := by
  unfold G
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, max_eq_left hs]
  exact mul_le_mul_of_nonneg_left (T_norm_le hT hs x) (Real.exp_pos _).le

theorem G_int (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T) {lam : ℝ}
    (hlam : 0 < lam) (x : E) : IntegrableOn (G T lam x) (Ioi 0) := by
  refine Integrable.mono' (g := fun s => Real.exp (-lam * s) * ‖x‖)
    ((exp_neg_integrableOn_Ioi 0 hlam).mul_const _) (G_cont hT lam x).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact G_norm hT lam x (le_of_lt hs)

theorem G_add (lam : ℝ) (x y : E) : G T lam (x + y) = G T lam x + G T lam y := by
  funext s; simp [G, smul_add]

theorem G_smul (lam : ℝ) (c : ℝ) (x : E) : G T lam (c • x) = c • G T lam x := by
  funext s; simp [G, smul_comm c]

noncomputable def Rint (T : ℝ → E →L[ℝ] E) (lam : ℝ) (x : E) : E :=
  ∫ s in Ioi (0:ℝ), G T lam x s

theorem Rint_norm (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T) {lam : ℝ}
    (hlam : 0 < lam) (x : E) : lam * ‖Rint T lam x‖ ≤ ‖x‖ := by
  unfold Rint
  have h1 : ‖∫ s in Ioi (0:ℝ), G T lam x s‖ ≤ ∫ s in Ioi (0:ℝ), Real.exp (-lam * s) * ‖x‖ := by
    refine norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hlam).mul_const _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact G_norm hT lam x (le_of_lt hs)
  have h2 : ∫ s in Ioi (0:ℝ), Real.exp (-lam * s) * ‖x‖ = ‖x‖ / lam := by
    rw [integral_mul_const, integral_exp_mul_Ioi (by linarith : -lam < 0)]
    simp only [mul_zero, Real.exp_zero]
    rw [neg_div_neg_eq]
    ring
  rw [h2] at h1
  calc lam * _ ≤ lam * (‖x‖ / lam) := mul_le_mul_of_nonneg_left h1 hlam.le
    _ = ‖x‖ := by field_simp

noncomputable def J (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T) {lam : ℝ}
    (hlam : 0 < lam) : E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun x => lam • Rint T lam x
      map_add' := fun x y => by
        show lam • Rint T lam (x + y) = lam • Rint T lam x + lam • Rint T lam y
        rw [← smul_add]
        congr 1
        unfold Rint
        rw [G_add]
        exact integral_add (G_int hT hlam x) (G_int hT hlam y)
      map_smul' := fun c x => by
        show lam • Rint T lam (c • x) = c • (lam • Rint T lam x)
        unfold Rint
        rw [G_smul, smul_comm c lam]
        congr 1
        exact integral_smul c (G T lam x) }
    1 (fun x => by
      show ‖lam • Rint T lam x‖ ≤ 1 * ‖x‖
      rw [norm_smul, Real.norm_of_nonneg hlam.le, one_mul]
      exact Rint_norm hT hlam x)

theorem J_apply (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T) {lam : ℝ}
    (hlam : 0 < lam) (x : E) : J hT hlam x = lam • Rint T lam x := rfl

theorem J_norm (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T) {lam : ℝ}
    (hlam : 0 < lam) : ‖J hT hlam‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem J_comm (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T) {lam : ℝ}
    (hlam : 0 < lam) {r : ℝ} (hr : 0 ≤ r) (x : E) : T r (J hT hlam x) = J hT hlam (T r x) := by
  rw [J_apply, J_apply, map_smul]
  congr 1
  unfold Rint
  rw [← ContinuousLinearMap.integral_comp_comm _ (G_int hT hlam x)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  simp only [G, map_smul]
  rw [T_comm hT hr (le_max_right _ _)]

theorem T_Rint_shift (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T) {lam : ℝ}
    (hlam : 0 < lam) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    T r (Rint T lam x) = Real.exp (lam * r) • ∫ s in Ioi r, G T lam x s := by
  unfold Rint
  rw [← ContinuousLinearMap.integral_comp_comm _ (G_int hT hlam x)]
  have : ∀ s ∈ Ioi (0:ℝ), T r (G T lam x s) = Real.exp (lam * r) • G T lam x (s + r) := by
    intro s hs
    have hs0 : (0:ℝ) < s := hs
    simp only [G, map_smul, smul_smul]
    rw [max_eq_left hs0.le, max_eq_left (by linarith : (0:ℝ) ≤ s + r)]
    rw [show T r (T s x) = T (s + r) x from by
      rw [T_comm hT hr hs0.le, ← ContinuousLinearMap.comp_apply, ← hT.2.1 s r hs0.le hr]]
    congr 1
    rw [← Real.exp_add]; congr 1; ring
  rw [setIntegral_congr_fun measurableSet_Ioi this, integral_smul]
  congr 1
  have := (measurePreserving_add_right volume r).setIntegral_preimage_emb
    (measurableEmbedding_addRight r) (G T lam x) (Ioi r)
  rw [preimage_add_const_Ioi, sub_self] at this
  exact this

theorem gen_J (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T) {lam : ℝ}
    (hlam : 0 < lam) (x : E) :
    Gen T (J hT hlam x) (lam • (J hT hlam x - x)) := by
  set I := Rint T lam x with hI
  have hGc := G_cont hT lam x
  have hG0 : G T lam x 0 = x := by simp [G, hT.1]
  have hΦ : HasDerivAt (fun u => ∫ s in (0:ℝ)..u, G T lam x s) x 0 := by
    have := (hGc.integral_hasStrictDerivAt 0 0).hasDerivAt
    rwa [hG0] at this
  have hΦs := hΦ.tendsto_slope_zero_right
  simp only [zero_add, intervalIntegral.integral_same, sub_zero] at hΦs
  have hE : HasDerivAt (fun r : ℝ => Real.exp (lam * r)) lam 0 := by
    have := ((hasDerivAt_id (0:ℝ)).const_mul lam).exp
    simpa using this
  have hEs := hE.tendsto_slope_zero_right
  simp only [zero_add, mul_zero, Real.exp_zero, smul_eq_mul] at hEs
  have hEc : Tendsto (fun r : ℝ => Real.exp (lam * r)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have : Tendsto (fun r : ℝ => Real.exp (lam * r)) (𝓝 (0:ℝ)) (𝓝 (Real.exp (lam * 0))) :=
      (by fun_prop : Continuous fun r : ℝ => Real.exp (lam * r)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun r : ℝ => lam • ((r⁻¹ * (Real.exp (lam * r) - 1)) • I -
      Real.exp (lam * r) • (r⁻¹ • ∫ s in (0:ℝ)..r, G T lam x s))) (𝓝[>] (0:ℝ))
      (𝓝 (lam • (lam • I - (1:ℝ) • x))) := by
    refine Tendsto.const_smul (Tendsto.sub ?_ ?_) lam
    · exact hEs.smul_const I
    · exact hEc.smul hΦs
  unfold Gen
  rw [J_apply]
  have htarget : lam • (lam • I - (1:ℝ) • x) = lam • (lam • Rint T lam x - x) := by
    simp [hI]
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0:ℝ) < r := hr
  have hshift := T_Rint_shift hT hlam x hr'.le
  have hsplit : ∫ s in Ioi r, G T lam x s = I - ∫ s in (0:ℝ)..r, G T lam x s := by
    have := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (f := G T lam x) ((G_int hT hlam x).mono_set Ioc_subset_Ioi_self)
      ((G_int hT hlam x).mono_set (Ioi_subset_Ioi hr'.le))
    rw [Ioc_union_Ioi_eq_Ioi hr'.le] at this
    rw [intervalIntegral.integral_of_le hr'.le, hI]
    unfold Rint
    rw [this]; abel
  rw [map_smul, hshift, hsplit]
  module

/-- Approximate identity: `J_{n+1} x → x`. -/
theorem J_tendsto (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T) (x : E) :
    Tendsto (fun n : ℕ => J hT (Nat.cast_add_one_pos n) x) atTop (𝓝 x) := by
  have key : ∀ lam : ℝ, ∀ hlam : 0 < lam,
      J hT hlam x = ∫ u in Ioi (0:ℝ), G T lam x (lam⁻¹ * u) := by
    intro lam hlam
    rw [J_apply, Rint, integral_comp_mul_left_Ioi (G T lam x) 0 (inv_pos.2 hlam), mul_zero,
      inv_inv]
  have hlim : Tendsto (fun n : ℕ => ∫ u in Ioi (0:ℝ), G T ((n:ℝ)+1) x (((n:ℝ)+1)⁻¹ * u))
      atTop (𝓝 (∫ u in Ioi (0:ℝ), Real.exp (-u) • x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u => Real.exp (-u) * ‖x‖)
      (Eventually.of_forall (fun n => ((G_cont hT _ x).comp
        (continuous_const.mul continuous_id)).aestronglyMeasurable)) ?_ ?_ ?_
    · refine Eventually.of_forall (fun n => ?_)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : (0:ℝ) < u := hu
      have hn : (0:ℝ) < (n:ℝ) + 1 := Nat.cast_add_one_pos n
      have := G_norm hT ((n:ℝ)+1) x (s := ((n:ℝ)+1)⁻¹ * u) (by positivity)
      have he : -((n:ℝ)+1) * (((n:ℝ)+1)⁻¹ * u) = -u := by field_simp
      rw [he] at this
      exact this
    · simpa using (exp_neg_integrableOn_Ioi 0 one_pos).mul_const ‖x‖
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : (0:ℝ) < u := hu
      have hseq : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹ * u) atTop (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (fun n => ?_)⟩
        · have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const u
          simpa using this
        · show (0:ℝ) < ((n:ℝ)+1)⁻¹ * u
          have hn : (0:ℝ) < (n:ℝ) + 1 := Nat.cast_add_one_pos n
          positivity
      have h2 := (hT.2.2.2 x).comp hseq
      have h3 := (tendsto_const_nhds (x := Real.exp (-u))).smul h2
      refine h3.congr (fun n => ?_)
      have hn : (0:ℝ) < (n:ℝ) + 1 := Nat.cast_add_one_pos n
      simp only [Function.comp_apply, G]
      rw [max_eq_left (by positivity)]
      congr 2
      field_simp
  rw [integral_smul_const, integral_exp_neg_Ioi_zero, one_smul] at hlim
  refine hlim.congr (fun n => (key _ _).symm)

end Res

section Cone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (P : E → Prop)

theorem exp_smul_pos (hP0 : P 0) (hPadd : ∀ x y, P x → P y → P (x + y))
    (hPsmul : ∀ {c : ℝ} {x}, 0 ≤ c → P x → P (c • x)) (hPcl : IsClosed {x | P x})
    {K : E →L[ℝ] E} (hK : ∀ y, P y → P (K y))
    {c : ℝ} (hc : 0 ≤ c) {y : E} (hy : P y) : P (NormedSpace.exp (c • K) y) := by
  have hpow : ∀ n : ℕ, ∀ y, P y → P (((c • K) ^ n) y) := by
    intro n
    induction n with
    | zero => intro y hy; exact hy
    | succ n ih =>
      intro y hy
      rw [pow_succ]
      exact ih _ (hPsmul hc (hK y hy))
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (c • K)
  have hs2 := (ContinuousLinearMap.apply ℝ E y).hasSum hs
  refine hPcl.mem_of_tendsto hs2.tendsto_sum_nat (Eventually.of_forall fun n => ?_)
  refine Finset.sum_induction _ P hPadd hP0 (fun i _ => ?_)
  exact hPsmul (by positivity) (hpow i y hy)

theorem exp_one_smul (x : ℝ) :
    NormedSpace.exp (x • (1 : E →L[ℝ] E)) = Real.exp x • (1 : E →L[ℝ] E) := by
  have := NormedSpace.algebraMap_exp_comm (𝔸 := E →L[ℝ] E) x
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at this
  rw [← this, Real.exp_eq_exp_ℝ]

theorem exp_B (K : E →L[ℝ] E) (r c : ℝ) :
    NormedSpace.exp (r • (c • (K - 1))) =
      Real.exp (-(r * c)) • NormedSpace.exp ((r * c) • K) := by
  have e : r • (c • (K - 1)) = (r * c) • K + (-(r * c)) • (1 : E →L[ℝ] E) := by
    rw [smul_sub, smul_sub, smul_smul, smul_smul, neg_smul, ← sub_eq_add_neg]
  have hmem : ∀ A : E →L[ℝ] E, A ∈ Metric.eball (0 : E →L[ℝ] E)
      (NormedSpace.expSeries ℝ (E →L[ℝ] E)).radius := by
    intro A
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  rw [e, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    ((Commute.one_right _).smul_right _) (hmem _) (hmem _), exp_one_smul, mul_smul_comm,
    mul_one]

theorem norm_exp_le (K : E →L[ℝ] E) (hK : ‖K‖ ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    ‖NormedSpace.exp (a • K)‖ ≤ Real.exp a := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (a • K)
  have hr : HasSum (fun n : ℕ => (n.factorial⁻¹ : ℝ) • a ^ n) (Real.exp a) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a
  rw [← hs.tsum_eq]
  refine tsum_of_norm_bounded hr (fun n => ?_)
  rw [norm_smul, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  have hnorm : ‖a • K‖ ≤ a := by
    rw [norm_smul, Real.norm_of_nonneg ha]; exact mul_le_of_le_one_right ha hK
  have : ‖(a • K) ^ n‖ ≤ a ^ n := by
    rcases n with _ | n
    · rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    · exact (norm_pow_le' _ (Nat.succ_pos n)).trans
        (pow_le_pow_left₀ (norm_nonneg _) hnorm _)
  exact mul_le_mul_of_nonneg_left this (by positivity)

theorem norm_exp_B_le (K : E →L[ℝ] E) (hK : ‖K‖ ≤ 1) {r c : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ c) :
    ‖NormedSpace.exp (r • (c • (K - 1)))‖ ≤ 1 := by
  rw [exp_B, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-(r * c)) * ‖NormedSpace.exp ((r * c) • K)‖
      ≤ Real.exp (-(r * c)) * Real.exp (r * c) :=
        mul_le_mul_of_nonneg_left (norm_exp_le K hK (mul_nonneg hr hc)) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- Yosida-type comparison estimate. -/
theorem yosida_est {T : ℝ → E →L[ℝ] E}
    (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T)
    {B : E →L[ℝ] E} (hBc : ∀ s : ℝ, 0 ≤ s → ∀ y, B (T s y) = T s (B y))
    (hBn : ∀ r : ℝ, 0 ≤ r → ‖NormedSpace.exp (r • B)‖ ≤ 1) {z w : E} (hz : Gen T z w)
    {t : ℝ} (ht : 0 ≤ t) : ‖T t z - NormedSpace.exp (t • B) z‖ ≤ ‖w - B z‖ * t := by
  set φ : ℝ → E := fun s => NormedSpace.exp ((t - s) • B) (T s z) with hφdef
  have hexp : ∀ s, HasDerivAt (fun s : ℝ => NormedSpace.exp ((t - s) • B))
      (-(NormedSpace.exp ((t - s) • B) * B)) s := by
    intro s
    have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) B (t - s)
    have h2 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have := h1.scomp s h2
    simpa [Function.comp_def] using this
  have hφ : ∀ s ∈ Ico 0 t, HasDerivWithinAt φ
      (NormedSpace.exp ((t - s) • B) (T s (w - B z))) (Ici s) s := by
    intro s hs
    have h1 := (hexp s).hasDerivWithinAt (s := Ici s)
    have h2 := T_hasDerivWithinAt hT hz hs.1
    have := h1.clm_apply h2
    convert this using 1
    rw [ContinuousLinearMap.neg_apply]
    simp only [map_sub, ← hBc s hs.1]
    show _ = -(NormedSpace.exp ((t - s) • B) (B (T s z))) + _
    abel
  have hcont : ContinuousOn φ (Icc 0 t) := by
    have hc1 : Continuous (fun s : ℝ => NormedSpace.exp ((t - s) • B)) :=
      continuous_iff_continuousAt.2 (fun s => (hexp s).continuousAt)
    exact hc1.continuousOn.clm_apply ((T_cont hT z).mono Icc_subset_Ici_self)
  have hbound : ∀ s ∈ Ico 0 t,
      ‖NormedSpace.exp ((t - s) • B) (T s (w - B z))‖ ≤ ‖w - B z‖ := by
    intro s hs
    calc _ ≤ ‖NormedSpace.exp ((t - s) • B)‖ * ‖T s (w - B z)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖w - B z‖ :=
          mul_le_mul (hBn _ (by linarith [hs.2])) (T_norm_le hT hs.1 _) (norm_nonneg _)
            zero_le_one
      _ = _ := one_mul _
  have := norm_image_sub_le_of_norm_deriv_right_le_segment hcont hφ hbound t
    (right_mem_Icc.2 ht)
  simp only [hφdef, sub_self, zero_smul, NormedSpace.exp_zero, sub_zero, hT.1] at this
  exact this

theorem Gen_eq_zero {T : ℝ → E →L[ℝ] E} (hP0 : P 0)
    (hPpt : ∀ x, P x → P (-x) → x = 0)
    (HP : ∀ f g, Gen T f g → ∀ lam : ℝ, 0 < lam → P (lam • f - g) → P f)
    {d : E} {lam : ℝ} (hlam : 0 < lam) (h : Gen T d (lam • d)) : d = 0 := by
  have h1 := HP d _ h lam hlam (by rw [sub_self]; exact hP0)
  have h' := Gen_smul (-1) h
  have h2 := HP _ _ h' lam hlam (by rw [smul_comm, sub_self]; exact hP0)
  rw [neg_one_smul] at h2
  exact hPpt d h1 h2

theorem abstract_pos {T : ℝ → E →L[ℝ] E} (hP0 : P 0)
    (hPadd : ∀ x y, P x → P y → P (x + y))
    (hPsmul : ∀ {c : ℝ} {x}, 0 ≤ c → P x → P (c • x)) (hPcl : IsClosed {x | P x})
    (hPpt : ∀ x, P x → P (-x) → x = 0)
    (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T)
    (HP : ∀ f g, Gen T f g → ∀ lam : ℝ, 0 < lam → P (lam • f - g) → P f) :
    ∀ t : ℝ, 0 ≤ t → ∀ f, P f → P (T t f) := by
  intro t ht x hx
  have Jpos : ∀ {lam : ℝ} (hlam : 0 < lam) (y : E), P y → P (J hT hlam y) := by
    intro lam hlam y hy
    refine HP _ _ (gen_J hT hlam y) lam hlam ?_
    have : lam • J hT hlam y - lam • (J hT hlam y - y) = lam • y := by
      rw [smul_sub]; abel
    rw [this]
    exact hPsmul hlam.le hy
  have Jid : ∀ {lam : ℝ} (hlam : 0 < lam) {z w : E}, Gen T z w →
      J hT hlam w = lam • (J hT hlam z - z) := by
    intro lam hlam z w hz
    have h1 := gen_J hT hlam w
    have h2 := gen_J hT hlam z
    have h3 := Gen_smul lam (Gen_sub h2 hz)
    have h4 := Gen_sub h1 h3
    have h5 : lam • (J hT hlam w - w) - lam • (lam • (J hT hlam z - z) - w) =
        lam • (J hT hlam w - lam • (J hT hlam z - z)) := by
      simp only [smul_sub]; abel
    rw [h5] at h4
    exact sub_eq_zero.1 (Gen_eq_zero P hP0 hPpt HP hlam h4)
  have step1 : ∀ m : ℕ, P (T t (J hT (Nat.cast_add_one_pos m) x)) := by
    intro m
    set z := J hT (Nat.cast_add_one_pos m) x with hzdef
    set w := ((m:ℝ) + 1) • (z - x) with hwdef
    have hz : Gen T z w := gen_J hT _ x
    have hzpos : P z := Jpos _ x hx
    have hest : ∀ n : ℕ, ‖T t z - NormedSpace.exp
        (t • (((n:ℝ) + 1) • (J hT (Nat.cast_add_one_pos n) - 1))) z‖ ≤
        ‖w - J hT (Nat.cast_add_one_pos n) w‖ * t := by
      intro n
      have hBz : (((n:ℝ) + 1) • (J hT (Nat.cast_add_one_pos n) - 1)) z =
          J hT (Nat.cast_add_one_pos n) w :=
        (show (((n:ℝ) + 1) • (J hT (Nat.cast_add_one_pos n) - 1)) z =
          ((n:ℝ) + 1) • (J hT (Nat.cast_add_one_pos n) z - z) from rfl).trans (Jid _ hz).symm
      rw [← hBz]
      refine yosida_est hT ?_ ?_ hz ht
      · intro s hs y
        show ((n:ℝ) + 1) • (J hT (Nat.cast_add_one_pos n) (T s y) - T s y) =
          T s (((n:ℝ) + 1) • (J hT (Nat.cast_add_one_pos n) y - y))
        rw [map_smul, map_sub, J_comm hT _ hs]
      · intro r hr
        exact norm_exp_B_le _ (J_norm hT _) hr (Nat.cast_add_one_pos n).le
    have hconv : Tendsto (fun n : ℕ => NormedSpace.exp
        (t • (((n:ℝ) + 1) • (J hT (Nat.cast_add_one_pos n) - 1))) z) atTop (𝓝 (T t z)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hw := J_tendsto hT w
      have h0 : Tendsto (fun n : ℕ => ‖w - J hT (Nat.cast_add_one_pos n) w‖ * t) atTop
          (𝓝 (0 * t)) := by
        refine Tendsto.mul_const t ?_
        have := (tendsto_iff_norm_sub_tendsto_zero.1 hw)
        refine this.congr (fun n => ?_)
        rw [norm_sub_rev]
      rw [zero_mul] at h0
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
      rw [norm_sub_rev]
      exact hest n
    refine hPcl.mem_of_tendsto hconv (Eventually.of_forall fun n => ?_)
    show P (NormedSpace.exp (t • (((n:ℝ) + 1) • (J hT (Nat.cast_add_one_pos n) - 1))) z)
    rw [exp_B]
    exact hPsmul (Real.exp_pos _).le (exp_smul_pos P hP0 hPadd hPsmul hPcl
      (fun y hy => Jpos _ y hy) (mul_nonneg ht (Nat.cast_add_one_pos n).le) hzpos)
  have hlim := ((T t).continuous.tendsto x).comp (J_tendsto hT x)
  exact hPcl.mem_of_tendsto hlim (Eventually.of_forall step1)

end Cone

section Pos

variable {X : Type*} [TopologicalSpace X]

theorem pos_closed : IsClosed {f : X →ᵇ ℝ | ∀ p, 0 ≤ f p} := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter (fun p => isClosed_le continuous_const (continuous_eval_const p))

theorem pos_pt (f : X →ᵇ ℝ) (h1 : ∀ p, 0 ≤ f p) (h2 : ∀ p, 0 ≤ (-f) p) : f = 0 := by
  ext p
  have a := h1 p
  have b := h2 p
  rw [BoundedContinuousFunction.neg_apply] at b
  show f p = (0 : ℝ)
  linarith

theorem abstract_pos_bcf {T : ℝ → (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)}
    (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T)
    (HP : ∀ f g, Gen T f g → ∀ lam : ℝ, 0 < lam → (∀ p, 0 ≤ (lam • f - g) p) → ∀ p, 0 ≤ f p) :
    ∀ t : ℝ, 0 ≤ t → ∀ f : X →ᵇ ℝ, (∀ p, 0 ≤ f p) → ∀ p, 0 ≤ T t f p :=
  abstract_pos (fun f : X →ᵇ ℝ => ∀ p, 0 ≤ f p)
    (fun _ => le_rfl)
    (fun x y hx hy p => by rw [BoundedContinuousFunction.add_apply]; exact add_nonneg (hx p) (hy p))
    (fun {c} {x} hc hx p => by
      rw [BoundedContinuousFunction.smul_apply, smul_eq_mul]; exact mul_nonneg hc (hx p))
    pos_closed pos_pt hT HP

end Pos

section Graph

open EthierKurtz

theorem holder_congr {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {μ : ℝ}
    {f g : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ComponentHolder Ω μ f)
    (heq : ∀ x ∈ Ω, g x = f x) : ComponentHolder Ω μ g := by
  obtain ⟨hc, ρ₀, M, h1, h2, h3⟩ := hf
  refine ⟨hc.congr heq, ρ₀, M, h1, h2, fun ρ hρ hρ' x z hz y hy w hw => ?_⟩
  have hyΩ : y ∈ Ω := (connectedComponentIn_subset _ _ hy).1
  have hwΩ : w ∈ Ω := (connectedComponentIn_subset _ _ hw).1
  rw [heq y hyΩ, heq w hwΩ]
  exact h3 ρ hρ hρ' x z hz y hy w hw

theorem memG_add_const {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {μ : ℝ} {a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {fg : ((closure Ω) →ᵇ ℝ) × ((closure Ω) →ᵇ ℝ)}
    (h : fg ∈ obliqueDiffusionGraph Ω μ a b c) (k : ℝ) :
    (fg.1 + BoundedContinuousFunction.const _ k, fg.2) ∈ obliqueDiffusionGraph Ω μ a b c := by
  set F := closedRegionRestriction fg.1 with hF
  set F' := closedRegionRestriction (fg.1 + BoundedContinuousFunction.const (closure Ω) k)
    with hF'
  have hloc : ∀ x ∈ Ω, F' =ᶠ[𝓝 x] fun y => F y + k := by
    intro x hx
    filter_upwards [hΩ.mem_nhds hx] with y hy
    have hy' : y ∈ closure Ω := subset_closure hy
    simp [hF, hF', closedRegionRestriction, hy']
  have hd1 : ∀ x ∈ Ω, fderiv ℝ F' x = fderiv ℝ F x := by
    intro x hx
    rw [(hloc x hx).fderiv_eq, fderiv_add_const]
  have hd1' : ∀ x ∈ Ω, fderiv ℝ F' =ᶠ[𝓝 x] fderiv ℝ F := by
    intro x hx
    filter_upwards [hΩ.mem_nhds hx] with y hy using hd1 y hy
  have hd2 : ∀ x ∈ Ω, ∀ v w : EuclideanSpace ℝ (Fin d),
      fderiv ℝ (fun y => fderiv ℝ F' y v) x w = fderiv ℝ (fun y => fderiv ℝ F y v) x w := by
    intro x hx v w
    have : (fun y => fderiv ℝ F' y v) =ᶠ[𝓝 x] (fun y => fderiv ℝ F y v) :=
      (hd1' x hx).mono (fun y hy => by simp only [hy])
    rw [this.fderiv_eq]
  simp only [obliqueDiffusionGraph, Set.mem_setOf_eq] at h ⊢
  rw [← hF] at h
  rw [← hF']
  obtain ⟨⟨hcd, hhol⟩, hg, Jf, hJc, hJ, hJb⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_, Jf, hJc, ?_, hJb⟩
  · exact (hcd.add contDiffOn_const).congr (fun x hx => (hloc x hx).eq_of_nhds)
  · intro i j
    exact holder_congr (hhol i j) (fun x hx => hd2 x hx _ _)
  · intro x hx
    rw [hg x hx]
    simp only [hd2 x hx, hd1 x hx]
  · intro x hx
    rw [hd1 _ hx]
    exact hJ x hx

end Graph

end EK376

open EthierKurtz Filter Topology BoundedContinuousFunction in
theorem solution (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (helliptic : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i)
    (T : ℝ → ((closure Ω) →ᵇ ℝ) →L[ℝ] ((closure Ω) →ᵇ ℝ))
    (hT : IsStronglyContinuousContractionSemigroup T)
    (hgen : ∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
      (𝓝[>] (0 : ℝ)) (𝓝 g) ↔
        (f, g) ∈ closure (obliqueDiffusionGraph Ω μ a b c))
    (hres : ∀ fg ∈ obliqueDiffusionGraph Ω μ a b c, ∀ lam : ℝ, 0 < lam →
      (∀ x, 0 ≤ (lam • fg.1 - fg.2) x) → ∀ x, 0 ≤ fg.1 x) :
    ∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x := by
  refine EK376.abstract_pos_bcf hT ?_
  intro f g hfg lam hlam hpos
  have hmem := (hgen f g).1 hfg
  rw [mem_closure_iff_seq_limit] at hmem
  obtain ⟨u, hu, hlim⟩ := hmem
  set e : ℕ → ℝ := fun k => ‖(lam • (u k).1 - (u k).2) - (lam • f - g)‖ with he
  have hvpos : ∀ k, ∀ p, 0 ≤ ((u k).1 + BoundedContinuousFunction.const (closure Ω) (e k / lam)) p := by
    intro k
    refine hres _ (EK376.memG_add_const hopen (hu k) (e k / lam)) lam hlam ?_
    intro p
    have hd := BoundedContinuousFunction.norm_coe_le_norm
      ((lam • (u k).1 - (u k).2) - (lam • f - g)) p
    rw [Real.norm_eq_abs] at hd
    have hd2 := (abs_le.1 hd).1
    have hp := hpos p
    have hlk : lam * (e k / lam) = e k := by field_simp
    simp only [BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_smul,
      BoundedContinuousFunction.coe_add, BoundedContinuousFunction.const_apply',
      Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hd2 hp ⊢
    rw [mul_add, hlk]
    have : e k = ‖(lam • (u k).1 - (u k).2) - (lam • f - g)‖ := rfl
    linarith
  have h1 : Tendsto (fun k => (u k).1) atTop (𝓝 f) := (continuous_fst.tendsto (f, g)).comp hlim
  have h2 : Tendsto (fun k => (u k).2) atTop (𝓝 g) := (continuous_snd.tendsto (f, g)).comp hlim
  have he0 : Tendsto e atTop (𝓝 0) := by
    have := (((h1.const_smul lam).sub h2).sub_const (lam • f - g)).norm
    simpa [he] using this
  intro p
  have hconv : Tendsto (fun k => ((u k).1 + BoundedContinuousFunction.const (closure Ω) (e k / lam)) p)
      atTop (𝓝 (f p + 0 / lam)) := by
    simp only [BoundedContinuousFunction.coe_add, BoundedContinuousFunction.const_apply',
      Pi.add_apply]
    exact (((continuous_eval_const p).tendsto f).comp h1).add (he0.div_const lam)
  rw [zero_div, add_zero] at hconv
  exact ge_of_tendsto hconv (Eventually.of_forall (fun k => hvpos k p))
