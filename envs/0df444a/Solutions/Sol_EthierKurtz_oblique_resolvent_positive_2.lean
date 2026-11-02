-- Prove2me | solution 2 for EthierKurtz.oblique_resolvent_positive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-01T21:52:29.808461+00:00
-- url     : https://prove2.me/submissions/48940c9f-9485-4e5f-8f91-740096afaae4

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Theorems.Thm_EthierKurtz_oblique_dissipative_estimate

set_option autoImplicit false

open Filter
open scoped Topology BoundedContinuousFunction

namespace P2a6a2cc1

open EthierKurtz

variable {d : ℕ}


lemma restr_lin {Ω : Set (EuclideanSpace ℝ (Fin d))} (c₁ c₂ : ℝ) (f₁ f₂ : (closure Ω) →ᵇ ℝ) :
    closedRegionRestriction (c₁ • f₁ + c₂ • f₂) =
      fun y => c₁ * closedRegionRestriction f₁ y + c₂ * closedRegionRestriction f₂ y := by
  funext y
  unfold closedRegionRestriction
  split_ifs <;> simp

lemma restr_zero {Ω : Set (EuclideanSpace ℝ (Fin d))} :
    closedRegionRestriction (0 : (closure Ω) →ᵇ ℝ) = fun _ => 0 := by
  funext y
  unfold closedRegionRestriction
  split_ifs <;> simp

lemma compHolder_congr {Ω : Set (EuclideanSpace ℝ (Fin d))} {μ : ℝ} {F G : (EuclideanSpace ℝ (Fin d)) → ℝ} (hF : ComponentHolder Ω μ F)
    (h : ∀ x ∈ Ω, G x = F x) : ComponentHolder Ω μ G := by
  obtain ⟨hc, ρ₀, M, hρ, hM, hb⟩ := hF
  refine ⟨hc.congr h, ρ₀, M, hρ, hM, fun ρ h0 h1 x z hz y hy w hw => ?_⟩
  have hyΩ : y ∈ Ω := (connectedComponentIn_subset _ _ hy).1
  have hwΩ : w ∈ Ω := (connectedComponentIn_subset _ _ hw).1
  rw [h y hyΩ, h w hwΩ]
  exact hb ρ h0 h1 x z hz y hy w hw

lemma compHolder_lin {Ω : Set (EuclideanSpace ℝ (Fin d))} {μ : ℝ} (hμ : 0 < μ) {F G : (EuclideanSpace ℝ (Fin d)) → ℝ}
    (hF : ComponentHolder Ω μ F) (hG : ComponentHolder Ω μ G) (c₁ c₂ : ℝ) :
    ComponentHolder Ω μ (fun x => c₁ * F x + c₂ * G x) := by
  obtain ⟨hcF, ρ₁, M₁, hρ₁, hM₁, hb₁⟩ := hF
  obtain ⟨hcG, ρ₂, M₂, hρ₂, hM₂, hb₂⟩ := hG
  refine ⟨(continuousOn_const.mul hcF).add (continuousOn_const.mul hcG), min ρ₁ ρ₂,
    |c₁| * M₁ + |c₂| * M₂, lt_min hρ₁ hρ₂, by positivity, ?_⟩
  intro ρ h0 h1 x z hz y hy w hw
  have e1 := hb₁ ρ h0 (h1.trans (min_le_left _ _)) x z hz y hy w hw
  have e2 := hb₂ ρ h0 (h1.trans (min_le_right _ _)) x z hz y hy w hw
  have hp : 0 ≤ ρ ^ μ := Real.rpow_nonneg h0.le _
  calc |(c₁ * F y + c₂ * G y) - (c₁ * F w + c₂ * G w)|
      = |c₁ * (F y - F w) + c₂ * (G y - G w)| := by ring_nf
    _ ≤ |c₁ * (F y - F w)| + |c₂ * (G y - G w)| := abs_add_le _ _
    _ = |c₁| * |F y - F w| + |c₂| * |G y - G w| := by rw [abs_mul, abs_mul]
    _ ≤ |c₁| * (M₁ * ρ ^ μ) + |c₂| * (M₂ * ρ ^ μ) := by
        gcongr
    _ = (|c₁| * M₁ + |c₂| * M₂) * ρ ^ μ := by ring

/-- First derivatives of a linear combination on an open set. -/
lemma fderiv_lin {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) {F G : (EuclideanSpace ℝ (Fin d)) → ℝ} (hF : ContDiffOn ℝ 2 F U)
    (hG : ContDiffOn ℝ 2 G U) (c₁ c₂ : ℝ) {y : (EuclideanSpace ℝ (Fin d))} (hy : y ∈ U) :
    fderiv ℝ (fun y => c₁ * F y + c₂ * G y) y = c₁ • fderiv ℝ F y + c₂ • fderiv ℝ G y := by
  have dF : DifferentiableAt ℝ F y :=
    (hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  have dG : DifferentiableAt ℝ G y :=
    (hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  rw [fderiv_fun_add (dF.const_mul c₁) (dG.const_mul c₂), fderiv_const_mul dF,
    fderiv_const_mul dG]

/-- Second partials of a linear combination on an open set. -/
lemma partial2_lin {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) {F G : (EuclideanSpace ℝ (Fin d)) → ℝ} (hF : ContDiffOn ℝ 2 F U)
    (hG : ContDiffOn ℝ 2 G U) (c₁ c₂ : ℝ) {x : (EuclideanSpace ℝ (Fin d))} (hx : x ∈ U) (i j : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ (fun y => c₁ * F y + c₂ * G y) y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)
      = c₁ * fderiv ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1)
        + c₂ * fderiv ℝ (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1) := by
  have DF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (hU.mem_nhds hx)
  have DG : DifferentiableAt ℝ (fderiv ℝ G) x :=
    ((hG.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (hU.mem_nhds hx)
  have hev : (fun y => fderiv ℝ (fun y => c₁ * F y + c₂ * G y) y (EuclideanSpace.single j 1))
      =ᶠ[𝓝 x] (fun y => c₁ * fderiv ℝ F y (EuclideanSpace.single j 1)
        + c₂ * fderiv ℝ G y (EuclideanSpace.single j 1)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [fderiv_lin hU hF hG c₁ c₂ hy]
    simp
  rw [hev.fderiv_eq]
  have dFj : DifferentiableAt ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x :=
    DF.clm_apply (differentiableAt_const _)
  have dGj : DifferentiableAt ℝ (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) x :=
    DG.clm_apply (differentiableAt_const _)
  rw [fderiv_fun_add (dFj.const_mul c₁) (dGj.const_mul c₂), fderiv_const_mul dFj,
    fderiv_const_mul dGj]
  simp

/-- The exact graph is closed under linear combinations. -/
lemma graph_lin {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ)
    {a : (EuclideanSpace ℝ (Fin d)) → Matrix (Fin d) (Fin d) ℝ} {b c : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d))}
    {p q : ((closure Ω) →ᵇ ℝ) × ((closure Ω) →ᵇ ℝ)}
    (hp : p ∈ obliqueDiffusionGraph Ω μ a b c) (hq : q ∈ obliqueDiffusionGraph Ω μ a b c)
    (c₁ c₂ : ℝ) : c₁ • p + c₂ • q ∈ obliqueDiffusionGraph Ω μ a b c := by
  simp only [obliqueDiffusionGraph, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd] at hp hq ⊢
  obtain ⟨⟨hF, hF2⟩, hFg, J₁, hJ₁c, hJ₁Ω, hJ₁b⟩ := hp
  obtain ⟨⟨hG, hG2⟩, hGg, J₂, hJ₂c, hJ₂Ω, hJ₂b⟩ := hq
  rw [restr_lin, restr_lin]
  set F := closedRegionRestriction p.1
  set G := closedRegionRestriction q.1
  refine ⟨⟨(contDiffOn_const.mul hF).add (contDiffOn_const.mul hG), fun i j => ?_⟩, ?_, ?_⟩
  · exact compHolder_congr (compHolder_lin hμ (hF2 i j) (hG2 i j) c₁ c₂)
      (fun x hx => partial2_lin hopen hF hG c₁ c₂ hx i j)
  · intro x hx
    beta_reduce
    rw [hFg x hx, hGg x hx, fderiv_lin hopen hF hG c₁ c₂ hx]
    simp only [partial2_lin hopen hF hG c₁ c₂ hx, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    simp only [mul_left_comm _ c₁, mul_left_comm _ c₂, ← Finset.mul_sum]
    ring
  · refine ⟨fun x => c₁ • J₁ x + c₂ • J₂ x, (hJ₁c.const_smul c₁).add (hJ₂c.const_smul c₂),
      fun x hx => ?_, fun x hx => ?_⟩
    · show c₁ • J₁ x + c₂ • J₂ x = _
      rw [hJ₁Ω x hx, hJ₂Ω x hx, fderiv_lin hopen hF hG c₁ c₂ hx]
    · simp [hJ₁b x hx, hJ₂b x hx]

lemma restr_one_ev {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω)
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ Ω) :
    closedRegionRestriction (1 : (closure Ω) →ᵇ ℝ) =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
  filter_upwards [hopen.mem_nhds hy] with z hz
  unfold closedRegionRestriction
  rw [dif_pos (subset_closure hz)]
  rfl

lemma restr_one_fderiv {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω)
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ Ω) :
    fderiv ℝ (closedRegionRestriction (1 : (closure Ω) →ᵇ ℝ)) y = 0 := by
  rw [(restr_one_ev hopen hy).fderiv_eq]
  exact fderiv_const_apply _

lemma restr_one_partial2 {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) (v w : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun y => fderiv ℝ (closedRegionRestriction (1 : (closure Ω) →ᵇ ℝ)) y v) x w
      = 0 := by
  have hev : (fun y => fderiv ℝ (closedRegionRestriction (1 : (closure Ω) →ᵇ ℝ)) y v)
      =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hx] with z hz
    rw [restr_one_fderiv hopen hz]
    rfl
  rw [hev.fderiv_eq]
  simp

/-- The constant one, with image zero, lies in the exact graph. -/
lemma graph_one {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω) {μ : ℝ}
    {a : (EuclideanSpace ℝ (Fin d)) → Matrix (Fin d) (Fin d) ℝ}
    {b c : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d))} :
    ((1 : (closure Ω) →ᵇ ℝ), (0 : (closure Ω) →ᵇ ℝ)) ∈ obliqueDiffusionGraph Ω μ a b c := by
  simp only [obliqueDiffusionGraph, Set.mem_ofPred_eq]
  refine ⟨⟨?_, fun i j => ?_⟩, ?_, ⟨fun _ => 0, continuous_const, fun x hx => ?_,
    fun x _ => rfl⟩⟩
  · exact (contDiffOn_const (c := (1 : ℝ))).congr (fun y hy => (restr_one_ev hopen hy).eq_of_nhds)
  · refine compHolder_congr (F := fun _ => 0) ⟨continuousOn_const, 1, 0, one_pos, le_rfl, ?_⟩ ?_
    · intro ρ _ _ x z _ y _ w _; simp
    · intro x hx; exact restr_one_partial2 hopen hx _ _
  · intro x hx
    rw [restr_zero]
    simp only [restr_one_partial2 hopen hx, restr_one_fderiv hopen hx, mul_zero,
      Finset.sum_const_zero, ContinuousLinearMap.zero_apply, add_zero]
  · exact (restr_one_fderiv hopen hx).symm

end P2a6a2cc1


open EthierKurtz in
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
      ε ≤ ∑ i, c x i * normal x i) :
    ∀ fg ∈ obliqueDiffusionGraph Ω μ a b c, ∀ lam : ℝ, 0 < lam →
      (∀ x, 0 ≤ (lam • fg.1 - fg.2) x) → ∀ x, 0 ≤ fg.1 x := by
  intro fg hfg lam hlam hpos x
  have hdis := EthierKurtz.oblique_dissipative_estimate n hd Ω hbounded hconnected hopen μ hμ
    hboundary a b c normal ha haHolder hbHolder helliptic hc hnormal hoblique
  set f := fg.1 with hf
  set g := fg.2 with hg
  set H : (closure Ω) →ᵇ ℝ := lam • f - g with hH
  set C : ℝ := ‖f‖ + ‖H‖ / lam + 1 with hC
  have hCpos : 0 < C := by positivity
  have hmem : (1 : ℝ) • fg + (-C) • (((1 : (closure Ω) →ᵇ ℝ), (0 : (closure Ω) →ᵇ ℝ))) ∈
      obliqueDiffusionGraph Ω μ a b c :=
    P2a6a2cc1.graph_lin hopen hμ.1 hfg (P2a6a2cc1.graph_one hopen) 1 (-C)
  have h1 := hdis _ (subset_closure hmem) lam hlam
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, one_smul,
    smul_zero, add_zero] at h1
  rw [← hf, ← hg] at h1
  -- upper bound for the right-hand side
  have hHle : ∀ y, H y ≤ lam * C := by
    intro y
    have e1 : H y ≤ ‖H‖ := (Real.le_norm_self _).trans (H.norm_coe_le_norm y)
    have e2 : ‖H‖ / lam * lam = ‖H‖ := div_mul_cancel₀ _ hlam.ne'
    have e3 : 0 ≤ ‖f‖ := norm_nonneg _
    nlinarith
  have hR : ‖lam • (f + (-C) • (1 : (closure Ω) →ᵇ ℝ)) - g‖ ≤ lam * C := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun y => ?_
    have hy : (lam • (f + (-C) • (1 : (closure Ω) →ᵇ ℝ)) - g) y = H y - lam * C := by
      simp only [hH, BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_smul,
        BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_one, Pi.sub_apply,
        Pi.add_apply, Pi.one_apply, smul_eq_mul]
      ring
    rw [hy, Real.norm_eq_abs, abs_le]
    have := hpos y
    have h2 := hHle y
    have h3 : 0 ≤ H y := by simpa [hH] using this
    constructor <;> linarith
  -- lower bound for the left-hand side
  have hL : C - f x ≤ ‖f + (-C) • (1 : (closure Ω) →ᵇ ℝ)‖ := by
    have e1 : (f + (-C) • (1 : (closure Ω) →ᵇ ℝ)) x = f x - C := by
      simp only [BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_smul,
        BoundedContinuousFunction.coe_one, Pi.add_apply, Pi.smul_apply, Pi.one_apply,
        smul_eq_mul]
      ring
    have e2 := (f + (-C) • (1 : (closure Ω) →ᵇ ℝ)).norm_coe_le_norm x
    rw [e1, Real.norm_eq_abs] at e2
    exact (neg_le_abs _).trans_eq' (by ring) |>.trans e2
  have key : lam * (C - f x) ≤ lam * C :=
    (mul_le_mul_of_nonneg_left hL hlam.le).trans (h1.trans hR)
  nlinarith
