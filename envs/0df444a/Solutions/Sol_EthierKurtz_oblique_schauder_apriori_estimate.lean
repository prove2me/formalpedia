-- Prove2me | solution 1 for EthierKurtz.oblique_schauder_apriori_estimate
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T05:41:40.987815+00:00
-- url     : https://prove2.me/submissions/3c3435fe-9753-42b5-8a4b-43a0605239a8

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Definitions.Def_EthierKurtz_closedRegionRestriction

set_option autoImplicit false
set_option linter.unusedVariables false

open Filter
open scoped Topology BoundedContinuousFunction

namespace P9877ba46

open EthierKurtz

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E1 := EuclideanSpace ℝ (Fin 1)

noncomputable def b0 : E2 := EuclideanSpace.single 0 1
noncomputable def e1 : E2 := EuclideanSpace.single 1 1

lemma nsq2 (y : E2) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

lemma nsq1 (z : E1) : ‖z‖ ^ 2 = z 0 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one]

noncomputable def u (z : E1) : ℝ := Real.sqrt (1 - z 0 ^ 2) - 1

def D : Set E1 := {z | z 0 ^ 2 < 3 / 4}
def V : Set E1 := {z | z 0 ^ 2 < 1}

noncomputable def cm (z : E1) : E2 :=
  WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i))

lemma cm0 (z : E1) : cm z 0 = z 0 := rfl
lemma cm1 (z : E1) : cm z 1 = u z := rfl

lemma cm_eq (z : E1) : cm z = (z 0) • b0 + (u z) • e1 := by
  ext i; fin_cases i
  · simp [cm0, b0, e1]
  · simp [cm1, b0, e1]

lemma cd_proj : ContDiff ℝ 3 (fun z : E1 => z 0) :=
  (EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ).contDiff

lemma isOpenV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
lemma isOpenD : IsOpen D := isOpen_lt (by fun_prop) continuous_const
lemma DsubV : D ⊆ V := fun z (hz : z 0 ^ 2 < 3 / 4) => show z 0 ^ 2 < 1 by linarith
lemma zeroD : (0 : E1) ∈ D := show (0 : E1) 0 ^ 2 < 3 / 4 by simp

lemma convD : Convex ℝ D := by
  intro y hy w hw a b ha hb hab
  have hy' : y 0 ^ 2 < 3 / 4 := hy
  have hw' : w 0 ^ 2 < 3 / 4 := hw
  show (a • y + b • w) 0 ^ 2 < 3 / 4
  have : (a • y + b • w) 0 = a * y 0 + b * w 0 := by simp
  rw [this]
  have hb' : b = 1 - a := by linarith
  subst hb'
  have key : (a * y 0 + (1 - a) * w 0) ^ 2 =
      a * y 0 ^ 2 + (1 - a) * w 0 ^ 2 - a * (1 - a) * (y 0 - w 0) ^ 2 := by ring
  have k1 : 0 ≤ a * (1 - a) * (y 0 - w 0) ^ 2 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  set m := max (y 0 ^ 2) (w 0 ^ 2)
  have hm : m < 3 / 4 := max_lt hy' hw'
  have k2 : a * y 0 ^ 2 ≤ a * m := mul_le_mul_of_nonneg_left (le_max_left _ _) ha
  have k3 : (1 - a) * w 0 ^ 2 ≤ (1 - a) * m := mul_le_mul_of_nonneg_left (le_max_right _ _) hb
  nlinarith

lemma isConnD : IsConnected D := ⟨⟨0, zeroD⟩, convD.isPreconnected⟩

lemma u_cd : ContDiffOn ℝ 3 u V := by
  intro z hz
  have hz' : z 0 ^ 2 < 1 := hz
  apply ContDiffAt.contDiffWithinAt
  unfold u
  refine ContDiffAt.sub ?_ contDiffAt_const
  refine ContDiffAt.sqrt ?_ (by linarith)
  exact contDiffAt_const.sub (cd_proj.contDiffAt.pow 2)

lemma cm_cd : ContDiffOn ℝ 3 cm V := by
  have : cm = fun z => (z 0) • b0 + (u z) • e1 := funext cm_eq
  rw [this]
  exact (cd_proj.contDiffOn.smul contDiffOn_const).add (u_cd.smul contDiffOn_const)

lemma u0 : u 0 = 0 := by simp [u]

lemma du0 : fderiv ℝ u 0 = 0 := by
  apply IsLocalMax.fderiv_eq_zero
  refine Filter.Eventually.of_forall (fun z => ?_)
  show u z ≤ u 0
  rw [u0]; unfold u
  have : Real.sqrt (1 - z 0 ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (z 0)])
  linarith

/-! Lipschitz control of C¹ functions on D. -/

lemma Kcpt : IsCompact {z : E1 | z 0 ^ 2 ≤ 3 / 4} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : E1)) (r := 1)).subset ?_
    intro z (hz : z 0 ^ 2 ≤ 3 / 4)
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := nsq1 z
    nlinarith [norm_nonneg z]

lemma lip_of_C1 {g : E1 → ℝ} (hg : ContDiffOn ℝ 1 g V) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y ∈ D, ∀ w ∈ D, |g y - g w| ≤ L * ‖y - w‖ := by
  have hc := hg.continuousOn_fderiv_of_isOpen isOpenV le_rfl
  have hKV : {z : E1 | z 0 ^ 2 ≤ 3 / 4} ⊆ V := fun z (hz : z 0 ^ 2 ≤ 3 / 4) =>
    show z 0 ^ 2 < 1 by linarith
  obtain ⟨C, hC⟩ := Kcpt.exists_bound_of_continuousOn (hc.mono hKV)
  refine ⟨max C 0, le_max_right _ _, fun y hy w hw => ?_⟩
  have hdiff : ∀ x ∈ D, DifferentiableAt ℝ g x := fun x hx =>
    ((hg.differentiableOn one_ne_zero) x (DsubV hx)).differentiableAt
      (isOpenV.mem_nhds (DsubV hx))
  have hb : ∀ x ∈ D, ‖fderiv ℝ g x‖ ≤ max C 0 := fun x hx =>
    (hC x (le_of_lt (show x 0 ^ 2 < 3 / 4 from hx))).trans (le_max_left _ _)
  have := convD.norm_image_sub_le_of_norm_fderiv_le hdiff hb hw hy
  simpa [Real.norm_eq_abs] using this

lemma CH_of_C1 {g : E1 → ℝ} (hg : ContDiffOn ℝ 1 g V) : ComponentHolder D 1 g := by
  obtain ⟨L, hL0, hL⟩ := lip_of_C1 hg
  refine ⟨hg.continuousOn.mono DsubV, 1, 2 * L, one_pos, by positivity, ?_⟩
  intro ρ hρ _ x z _ y hy w hw
  have hy' := connectedComponentIn_subset _ _ hy
  have hw' := connectedComponentIn_subset _ _ hw
  rw [Real.rpow_one]
  have h1 : dist y x < ρ := hy'.2
  have h2 : dist w x < ρ := hw'.2
  have h3 : ‖y - w‖ ≤ 2 * ρ := by
    rw [← dist_eq_norm]
    calc dist y w ≤ dist y x + dist x w := dist_triangle _ _ _
      _ ≤ 2 * ρ := by rw [dist_comm x w]; linarith
  calc |g y - g w| ≤ L * ‖y - w‖ := hL y hy'.1 w hw'.1
    _ ≤ L * (2 * ρ) := by gcongr
    _ = 2 * L * ρ := by ring

lemma d1 {g : E1 → ℝ} {m n : WithTop ℕ∞} (hg : ContDiffOn ℝ n g V) (hmn : m + 1 ≤ n) (v : E1) :
    ContDiffOn ℝ m (fun x => fderiv ℝ g x v) V :=
  (hg.fderiv_of_isOpen isOpenV hmn).clm_apply contDiffOn_const

lemma CT_u : CTwiceHolder D 1 u := by
  refine ⟨(u_cd.of_le (by norm_num)).mono DsubV, fun i j => CH_of_C1 ?_⟩
  exact d1 (d1 (m := 2) u_cd (by norm_num) _) (by norm_num) _

lemma CO_of {φ : E1 → ℝ} (hφ : ContDiffOn ℝ 3 φ V) : COnceHolder D 1 φ :=
  ⟨(hφ.of_le (by norm_num)).mono DsubV, fun i => CH_of_C1 (d1 hφ (by norm_num) _)⟩

/-! The chart geometry of the unit circle. -/

lemma img (p : E2) (U : E2 ≃ₗᵢ[ℝ] E2) (hU : U p = e1) :
    (fun x => U (x - p)) '' (Metric.sphere 0 1 ∩ Metric.ball p 1) = cm '' D := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hx1
    rw [Metric.mem_ball, dist_eq_norm] at hx2
    set y := U (x - p) with hy
    have hn : ‖y‖ = ‖x - p‖ := by rw [hy, LinearIsometryEquiv.norm_map]
    have hye : y + e1 = U x := by rw [hy, map_sub, hU]; abel
    have hn2 : ‖y + e1‖ = 1 := by rw [hye, LinearIsometryEquiv.norm_map, hx1]
    have A := nsq2 (y + e1)
    have B := nsq2 y
    have c0 : (y + e1) 0 = y 0 := by simp [e1]
    have c1 : (y + e1) 1 = y 1 + 1 := by simp [e1]
    rw [hn2, c0, c1] at A
    have hlt : ‖y‖ ^ 2 < 1 := by nlinarith [norm_nonneg y]
    rw [B] at hlt
    have hpos : 0 ≤ y 1 + 1 := by nlinarith
    refine ⟨WithLp.toLp 2 (fun _ => y 0), ?_, ?_⟩
    · show y 0 ^ 2 < 3 / 4
      nlinarith
    · ext i; fin_cases i
      · rfl
      · show u (WithLp.toLp 2 (fun _ => y 0)) = y 1
        unfold u
        show Real.sqrt (1 - y 0 ^ 2) - 1 = y 1
        have : 1 - y 0 ^ 2 = (y 1 + 1) ^ 2 := by linarith
        rw [this, Real.sqrt_sq hpos]; ring
  · rintro ⟨z, hz, rfl⟩
    have hz' : z 0 ^ 2 < 3 / 4 := hz
    set s := Real.sqrt (1 - z 0 ^ 2) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = 1 - z 0 ^ 2 := Real.sq_sqrt (by linarith)
    have hs1 : 1 / 2 < s := by nlinarith
    have huz : u z = s - 1 := rfl
    refine ⟨p + U.symm (cm z), ⟨?_, ?_⟩, by simp⟩
    · rw [mem_sphere_zero_iff_norm]
      have hUx : U (p + U.symm (cm z)) = cm z + e1 := by
        rw [map_add, hU, LinearIsometryEquiv.apply_symm_apply]; abel
      rw [← LinearIsometryEquiv.norm_map U, hUx]
      have A := nsq2 (cm z + e1)
      have c0 : (cm z + e1) 0 = z 0 := by simp [e1, cm0]
      have c1 : (cm z + e1) 1 = s := by simp [e1, cm1, huz]
      rw [c0, c1] at A
      have : ‖cm z + e1‖ ^ 2 = 1 := by rw [A]; linarith
      have hn := norm_nonneg (cm z + e1)
      nlinarith
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, LinearIsometryEquiv.norm_map]
      have A := nsq2 (cm z)
      rw [cm0, cm1, huz] at A
      have : ‖cm z‖ ^ 2 < 1 := by rw [A]; nlinarith
      have hn := norm_nonneg (cm z)
      nlinarith

lemma e1_norm : ‖e1‖ = 1 := by simp [e1]

lemma exU (p : E2) (hp : ‖p‖ = 1) : ∃ U : E2 ≃ₗᵢ[ℝ] E2, U p = e1 :=
  ⟨Submodule.reflection (ℝ ∙ (p - e1))ᗮ, Submodule.reflection_sub (by rw [hp, e1_norm])⟩

lemma conn (p : E2) (U : E2 ≃ₗᵢ[ℝ] E2) (hU : U p = e1) :
    IsConnected (Metric.sphere (0 : E2) 1 ∩ Metric.ball p 1) := by
  have h : Metric.sphere (0 : E2) 1 ∩ Metric.ball p 1 =
      (fun y => p + U.symm y) '' (cm '' D) := by
    rw [← img p U hU, Set.image_image]
    simp
  rw [h]
  refine (isConnD.image cm (cm_cd.continuousOn.mono DsubV)).image _ ?_
  exact (continuous_const.add U.symm.continuous).continuousOn

lemma fr : frontier (Metric.ball (0 : E2) 1) = Metric.sphere 0 1 := frontier_ball _ one_ne_zero

lemma BCTH : BoundaryCTwiceHolder (n := 1) (Metric.ball (0 : E2) 1) 1 := by
  refine ⟨1, one_pos, fun p hp => ?_⟩
  rw [fr] at hp ⊢
  rw [mem_sphere_zero_iff_norm] at hp
  obtain ⟨U, hU⟩ := exU p hp
  exact ⟨U, D, u, isOpenD, zeroD, CT_u, u0, du0, conn p U hU, img p U hU⟩

lemma BCOH (i : Fin 2) : BoundaryCOnceHolder (n := 1) (Metric.ball (0 : E2) 1) 1 (fun x => x i) := by
  intro p hp
  rw [fr] at hp ⊢
  rw [mem_sphere_zero_iff_norm] at hp
  obtain ⟨U, hU⟩ := exU p hp
  refine ⟨1, one_pos, U, D, u, isOpenD, zeroD, CT_u, u0, du0, conn p U hU, img p U hU, ?_⟩
  apply CO_of
  have h1 : ContDiff ℝ 3 (fun x : E2 => x i) :=
    (EuclideanSpace.proj i : E2 →L[ℝ] ℝ).contDiff
  have h2 : ContDiff ℝ 3 (fun y : E2 => p + U.symm y) := contDiff_const.add U.symm.contDiff
  exact (h1.comp h2).comp_contDiffOn cm_cd

lemma inner_eq (x h : E2) : inner ℝ x h = ∑ i, x i * h i := by
  simp [PiLp.inner_apply, mul_comm]

lemma normal (x : E2) (hx : x ∈ frontier (Metric.ball (0 : E2) 1)) :
    IsOutwardUnitNormal (Metric.ball (0 : E2) 1) x x := by
  have hx' := hx
  rw [fr, mem_sphere_zero_iff_norm] at hx'
  refine ⟨hx, hx', Set.univ, isOpen_univ, Set.mem_univ _, fun y => ‖y‖ ^ 2 - 1, 2, two_pos,
    (contDiff_norm_sq ℝ).contDiffOn.sub contDiffOn_const, by simp [hx'], ?_, ?_⟩
  · intro y _
    rw [Metric.mem_ball, dist_zero_right]
    constructor
    · intro h; nlinarith [norm_nonneg y]
    · intro h; nlinarith [norm_nonneg y]
  · intro h
    have : fderiv ℝ (fun y : E2 => ‖y‖ ^ 2 - 1) x = 2 • innerSL ℝ x := by
      rw [fderiv_sub_const]; exact fderiv_norm_sq_apply x
    rw [this]
    simp [inner_eq]
    ring

/-! The counterexample: constant solutions. -/

lemma const_mem {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω) (μ : ℝ)
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (k : ℝ) :
    (BoundedContinuousFunction.const (closure Ω) k, (0 : (closure Ω) →ᵇ ℝ)) ∈
      obliqueDiffusionGraph Ω μ a b c := by
  set F := closedRegionRestriction (BoundedContinuousFunction.const (closure Ω) k) with hFdef
  have hF : ∀ x ∈ Ω, F =ᶠ[𝓝 x] fun _ => k := by
    intro x hx
    filter_upwards [hΩ.mem_nhds hx] with y hy
    simp [hFdef, closedRegionRestriction, subset_closure hy]
  have hD1 : ∀ x ∈ Ω, fderiv ℝ F x = 0 := by
    intro x hx
    rw [(hF x hx).fderiv_eq]; simp
  have hD2 : ∀ x ∈ Ω, ∀ v w : EuclideanSpace ℝ (Fin d),
      fderiv ℝ (fun y => fderiv ℝ F y w) x v = 0 := by
    intro x hx v w
    have : (fun y => fderiv ℝ F y w) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      rw [hD1 y hy]; rfl
    rw [this.fderiv_eq]; simp
  have hg0 : ∀ x, closedRegionRestriction (0 : (closure Ω) →ᵇ ℝ) x = 0 := by
    intro x; unfold closedRegionRestriction; split_ifs <;> rfl
  refine ⟨⟨contDiffOn_const.congr (fun x hx => (hF x hx).eq_of_nhds), fun i j => ?_⟩, ?_, ?_⟩
  · refine ⟨continuousOn_const.congr (fun x hx => hD2 x hx _ _), 1, 0, one_pos, le_rfl, ?_⟩
    intro ρ _ _ x z _ y hy w hw
    have hy' := (connectedComponentIn_subset _ _ hy).1
    have hw' := (connectedComponentIn_subset _ _ hw).1
    show |fderiv ℝ (fun y => fderiv ℝ F y _) y _ - fderiv ℝ (fun y => fderiv ℝ F y _) w _| ≤ _
    rw [hD2 y hy', hD2 w hw']; simp
  · intro x hx
    show closedRegionRestriction (0 : (closure Ω) →ᵇ ℝ) x = _
    rw [hg0]
    show (0 : ℝ) = (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d,
          a x i j * fderiv ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1)) + fderiv ℝ F x (b x)
    simp [hD2 x hx, hD1 x hx]
  · refine ⟨fun _ => 0, continuous_const, fun x hx => (hD1 x hx).symm, fun x _ => rfl⟩

end P9877ba46

namespace P9877ba46

lemma CH_const {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ k : ℝ) :
    EthierKurtz.ComponentHolder Ω μ (fun _ => k) :=
  ⟨continuousOn_const, 1, 0, one_pos, le_rfl, fun _ _ _ _ _ _ _ _ _ _ => by simp⟩

lemma ell (θ : E2) (hθ : ‖θ‖ = 1) :
    (1 : ℝ) ≤ ∑ i, ∑ j, θ i * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j * θ j := by
  have h := nsq2 θ
  rw [hθ] at h
  simp [Fin.sum_univ_two, Matrix.one_apply]
  nlinarith

lemma obl (x : E2) (hx : x ∈ frontier (Metric.ball (0 : E2) 1)) :
    (1 : ℝ) ≤ ∑ i, x i * x i := by
  rw [fr, mem_sphere_zero_iff_norm] at hx
  have h := nsq2 x
  rw [hx] at h
  simp [Fin.sum_univ_two]
  nlinarith

end P9877ba46

open scoped Topology BoundedContinuousFunction in open EthierKurtz in
theorem solution : ¬ (∀ (n : ℕ) (hd : 2 ≤ n + 1)
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
      ε ≤ ∑ i, c x i * normal x i),
    ∃ lamstar : ℝ, 0 < lamstar ∧ ∃ C₀ : NNReal,
      ∀ (f h : (closure Ω) →ᵇ ℝ) (Ch : NNReal) (lam : ℝ),
        lamstar ≤ lam →
        HolderWith Ch ⟨μ, hμ.1.le⟩ ⇑h →
        (∃ g : (closure Ω) →ᵇ ℝ,
          (f, g) ∈ obliqueDiffusionGraph Ω μ a b c ∧ lam • f - g = h) →
        (∀ x : closure Ω,
          ‖⇑f x‖ + ∑ i : Fin (n + 1),
              ‖fderiv ℝ (closedRegionRestriction f) ↑x
                (EuclideanSpace.single i 1)‖ +
            ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              ‖fderiv ℝ (fun y => fderiv ℝ (closedRegionRestriction f) y
                (EuclideanSpace.single j 1)) ↑x
                (EuclideanSpace.single i 1)‖ ≤
            ↑(C₀ * (Ch + 1))) ∧
        HolderWith (C₀ * (Ch + 1)) ⟨μ, hμ.1.le⟩ (fun x : closure Ω =>
          ‖⇑f x‖ + ∑ i : Fin (n + 1),
              ‖fderiv ℝ (closedRegionRestriction f) ↑x
                (EuclideanSpace.single i 1)‖ +
            ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              ‖fderiv ℝ (fun y => fderiv ℝ (closedRegionRestriction f) y
                (EuclideanSpace.single j 1)) ↑x
                (EuclideanSpace.single i 1)‖)) := by
  intro H
  obtain ⟨lamstar, -, C₀, hC⟩ := H 1 le_rfl (Metric.ball (0 : P9877ba46.E2) 1)
    Metric.isBounded_ball (Metric.isConnected_ball one_pos) Metric.isOpen_ball 1 ⟨one_pos, le_rfl⟩
    P9877ba46.BCTH (fun _ => 1) (fun _ => 0) (fun x => x) (fun x => x)
    (fun _ _ => Matrix.PosSemidef.one) (fun i j => P9877ba46.CH_const _ _ _)
    (fun i => P9877ba46.CH_const _ _ _) ⟨1, one_pos, fun x _ θ hθ => P9877ba46.ell θ hθ⟩
    P9877ba46.BCOH P9877ba46.normal ⟨1, one_pos, P9877ba46.obl⟩
  set k : ℝ := (C₀ : ℝ) + 1 with hk
  have hmem := P9877ba46.const_mem (Metric.ball (0 : P9877ba46.E2) 1) Metric.isOpen_ball 1
    (fun _ => 1) (fun _ => 0) (fun x => x) k
  have hx0 : (0 : P9877ba46.E2) ∈ closure (Metric.ball (0 : P9877ba46.E2) 1) :=
    subset_closure (Metric.mem_ball_self one_pos)
  have hbd := (hC (BoundedContinuousFunction.const _ k)
    (BoundedContinuousFunction.const _ (lamstar * k)) 0 lamstar le_rfl HolderWith.const
    ⟨0, hmem, by ext x; simp⟩).1 ⟨0, hx0⟩
  have hs1 : 0 ≤ ∑ i : Fin 2, ‖fderiv ℝ (closedRegionRestriction
      (BoundedContinuousFunction.const (closure (Metric.ball (0 : P9877ba46.E2) 1)) k))
      (0 : P9877ba46.E2) (EuclideanSpace.single i 1)‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hs2 : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖fderiv ℝ (fun y => fderiv ℝ (closedRegionRestriction
      (BoundedContinuousFunction.const (closure (Metric.ball (0 : P9877ba46.E2) 1)) k)) y
      (EuclideanSpace.single j 1)) (0 : P9877ba46.E2) (EuclideanSpace.single i 1)‖ :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hk' : ‖(BoundedContinuousFunction.const
      (closure (Metric.ball (0 : P9877ba46.E2) 1)) k) ⟨0, hx0⟩‖ = k := by
    rw [BoundedContinuousFunction.const_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hC1 : ((C₀ * (0 + 1) : NNReal) : ℝ) = (C₀ : ℝ) := by simp
  rw [hk', hC1] at hbd
  linarith
