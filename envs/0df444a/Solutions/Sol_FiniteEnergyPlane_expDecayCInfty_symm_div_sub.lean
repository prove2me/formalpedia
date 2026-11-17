-- Prove2me | solution 1 for FiniteEnergyPlane.expDecayCInfty_symm_div_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T22:23:39.580023+00:00
-- url     : https://prove2.me/submissions/df7456d4-4910-480f-80c3-5e23da034cba

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_comp_left
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_congr
import Theorems.Thm_FiniteEnergyPlane_exists_logCoords_of_div_sub



/-!
# B2: decay is preserved by composition with a map asymptotic to `z ↦ κ z`.

The log chart and `cylInf` identities are copied from `Scratch/JWQ_L4` (namespace `QL`).
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Real

noncomputable section

namespace BT

lemma cylInf_eq_exp (s t : ℝ) :
    cylInf s t = Complex.exp (((2 * π : ℝ) : ℂ) * ((s : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold cylInf ccwLoop
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast; ring

lemma cylInf_ne_zero (s t : ℝ) : cylInf s t ≠ 0 := by
  rw [cylInf_eq_exp]; exact Complex.exp_ne_zero _

lemma cylInf_add (s t s' t' : ℝ) :
    cylInf (s + s') (t + t') = cylInf s t * cylInf s' t' := by
  rw [cylInf_eq_exp, cylInf_eq_exp, cylInf_eq_exp, ← Complex.exp_add]
  congr 1
  push_cast; ring

lemma cylInf_log_arg {z : ℂ} (hz : z ≠ 0) :
    cylInf (Real.log ‖z‖ / (2 * π)) (Complex.arg z / (2 * π)) = z := by
  unfold cylInf ccwLoop
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hπ, Real.exp_log (norm_pos_iff.2 hz), mul_div_cancel₀ _ hπ]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- `log(1 + ζ) / (2π)`. -/
def lchart (ζ : ℂ) : ℂ := Complex.log (1 + ζ) * (((2 * π : ℝ) : ℂ))⁻¹

lemma one_add_mem_slitPlane' {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 1 + ζ ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have := Complex.abs_re_le_norm ζ
  rw [Complex.add_re, Complex.one_re]
  linarith [neg_abs_le ζ.re]

lemma lchart_contDiffAt {ζ : ℂ} (hζ : ‖ζ‖ < 1) : ContDiffAt ℝ ∞ lchart ζ := by
  have hlog : ContDiffAt ℝ ∞ Complex.log (1 + ζ) :=
    (Complex.contDiffAt_log (one_add_mem_slitPlane' hζ)).restrict_scalars ℝ
  exact (hlog.comp ζ (contDiffAt_const.add contDiffAt_id)).mul contDiffAt_const

lemma lchart_contDiffOn : ContDiffOn ℝ ∞ lchart (ball (0 : ℂ) 1) := fun ζ hζ =>
  (lchart_contDiffAt (mem_ball_zero_iff.1 hζ)).contDiffWithinAt

lemma lchart_zero : lchart 0 = 0 := by simp [lchart]

lemma cylInf_mul_one_add (s t : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    cylInf s t * (1 + ζ) = cylInf (s + (lchart ζ).re) (t + (lchart ζ).im) := by
  have hne : 1 + ζ ≠ 0 := Complex.slitPlane_ne_zero (one_add_mem_slitPlane' hζ)
  have hre : 2 * π * (lchart ζ).re = (Complex.log (1 + ζ)).re := by
    simp only [lchart, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    field_simp
  have him : 2 * π * (lchart ζ).im = (Complex.log (1 + ζ)).im := by
    simp only [lchart, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add]
    field_simp
  unfold cylInf ccwLoop
  rw [← Complex.exp_log hne]
  simp only [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_mul]
    push_cast
    linarith [hre]
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_mul, zero_add]
    push_cast
    linarith [him]

/-- `z ↦ (Re z, Im z)` as a continuous linear map. -/
def reIm : ℂ →L[ℝ] ℝ × ℝ := Complex.reCLM.prod Complex.imCLM

@[simp] lemma reIm_apply (z : ℂ) : reIm z = (z.re, z.im) := rfl

/-- Eventual smallness from `C⁰` decay. -/
lemma eventually_norm_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ × ℝ → E} {b : ℝ} (hb : 0 < b) (ha : ExpDecayCInfty a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ s ≥ S, ∀ t : ℝ, ‖a (s, t)‖ < ε := by
  obtain ⟨C₀, s₁, hC₀⟩ := ha.2 0
  have htend : Tendsto (fun s : ℝ => |C₀| * Real.exp (-(b * s))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => Real.exp (-(b * s))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hb)
    simpa using h1.const_mul |C₀|
  obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 (htend.eventually (gt_mem_nhds hε))
  refine ⟨max s₁ s₂, fun s hs t => ?_⟩
  have h0 := hC₀ s ((le_max_left _ _).trans hs) t
  rw [norm_iteratedFDeriv_zero] at h0
  exact (h0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)).trans_lt
    (hs₂ s ((le_max_right _ _).trans hs))

/-- Log coordinates of a map asymptotic to `z ↦ κ z`: `χ(cylInf p) = cylInf (p + c + E p)` far out,
with `E` decaying like `e^{-bs}`. -/
lemma exists_logCoords_aux (χ : ℂ → ℂ) (κ : ℂ) (hκ : κ ≠ 0) (b : ℝ) (hb : 0 < b)
    (has : ExpDecayCInfty (fun p : ℝ × ℝ => χ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b) :
    ∃ (E : ℝ × ℝ → ℝ × ℝ) (S : ℝ), ExpDecayCInfty E b ∧ ∀ s ≥ S, ∀ t : ℝ,
      χ (cylInf s t) =
        cylInf ((s, t) + (Real.log ‖κ‖ / (2 * π), Complex.arg κ / (2 * π)) + E (s, t)).1
          ((s, t) + (Real.log ‖κ‖ / (2 * π), Complex.arg κ / (2 * π)) + E (s, t)).2 := by
  set a : ℝ × ℝ → ℂ := fun p => χ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ with ha
  -- `ζ = a / κ`
  have hζ : ExpDecayCInfty (fun p => (fun z : ℂ => z * κ⁻¹) (a p)) b :=
    expDecayCInfty_comp_left (fun z : ℂ => z * κ⁻¹) 1 one_pos
      (contDiff_id.mul contDiff_const).contDiffOn (by simp) a b hb has
  have hlc : ExpDecayCInfty (fun p => lchart (a p * κ⁻¹)) b :=
    expDecayCInfty_comp_left lchart 1 one_pos lchart_contDiffOn lchart_zero _ b hb hζ
  have hE : ExpDecayCInfty (fun p => reIm (lchart (a p * κ⁻¹))) b :=
    expDecayCInfty_comp_left reIm 1 one_pos reIm.contDiff.contDiffOn (map_zero _) _ b hb hlc
  obtain ⟨S, hS⟩ := eventually_norm_lt hb hζ one_pos
  refine ⟨fun p => reIm (lchart (a p * κ⁻¹)), S, hE, fun s hs t => ?_⟩
  have hsm : ‖a (s, t) * κ⁻¹‖ < 1 := hS s hs t
  have hc := cylInf_ne_zero s t
  have h1 : χ (cylInf s t) = cylInf s t * κ * (1 + a (s, t) * κ⁻¹) := by
    simp only [ha]
    field_simp
    ring
  rw [h1, ← cylInf_log_arg hκ, ← cylInf_add, cylInf_log_arg hκ, cylInf_mul_one_add _ _ hsm]
  simp only [reIm_apply, Prod.fst_add, Prod.snd_add]

end BT

end

end FiniteEnergyPlane

/-! # B1, layer A: helpers for the asymptotics of the inverse. -/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Nat Real

noncomputable section

namespace BT

/-- Faà di Bruno bound on open sets, in terms of global iterated derivatives. -/
lemma fdb {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} {X : E → F} {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f V) (hX : ContDiffOn ℝ ∞ X U) (hmaps : MapsTo X U V) {q : E}
    (hq : q ∈ U) {k : ℕ} {C D : ℝ} (hC : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f (X q)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i X q‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ k (fun y => f (X y)) q‖ ≤ k ! * C * D ^ k := by
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := k) (N := ∞) hf hX
    (by exact_mod_cast le_top) hV.uniqueDiffOn hU.uniqueDiffOn hmaps hq (C := C) (D := D)
    (fun i hi => by rw [iteratedFDerivWithin_of_isOpen i hV (hmaps hq)]; exact hC i hi)
    (fun i hi1 hi => by rw [iteratedFDerivWithin_of_isOpen i hU hq]; exact hD i hi1 hi)
  rwa [iteratedFDerivWithin_of_isOpen k hU hq] at key

/-- Iterated derivatives agree where two functions agree on an open set. -/
lemma iteratedFDeriv_congr_open {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F} {U : Set E} (hU : IsOpen U)
    (h : EqOn f g U) {q : E} (hq : q ∈ U) (k : ℕ) :
    iteratedFDeriv ℝ k f q = iteratedFDeriv ℝ k g q := by
  have h1 : f =ᶠ[𝓝 q] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hq) h
  exact (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) h1 k).self_of_nhds

/-- `C^∞` decay of `E` implies `C^∞` decay of `fderiv E`. -/
lemma expDecay_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E : ℝ × ℝ → F} {b : ℝ} (hE : ExpDecayCInfty E b) :
    ExpDecayCInfty (fderiv ℝ E) b := by
  obtain ⟨⟨s₀, hs⟩, hl⟩ := hE
  have hO : IsOpen (Ioi s₀ ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  refine ⟨⟨s₀, hs.fderiv_of_isOpen hO (by exact_mod_cast le_top)⟩, fun m => ?_⟩
  obtain ⟨C, s₁, hC⟩ := hl (m + 1)
  exact ⟨C, s₁, fun s hs t => by rw [norm_iteratedFDeriv_fderiv]; exact hC s hs t⟩

/-- Bounded derivatives from decay. -/
lemma bound_of_expDecay {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E : ℝ × ℝ → F} {b : ℝ} (hb : 0 ≤ b) (hE : ExpDecayCInfty E b) (k : ℕ) :
    ∃ B T : ℝ, 0 ≤ B ∧ ∀ i ≤ k, ∀ s ≥ T, ∀ t : ℝ, ‖iteratedFDeriv ℝ i E (s, t)‖ ≤ B := by
  choose Ci si hCi using hE.2
  refine ⟨∑ i ∈ Finset.range (k + 1), |Ci i|, max 0 (∑ i ∈ Finset.range (k + 1), |si i|),
    Finset.sum_nonneg fun _ _ => abs_nonneg _, fun i hi s hs t => ?_⟩
  have hmem : i ∈ Finset.range (k + 1) := Finset.mem_range.2 (by omega)
  have hsi : si i ≤ s := (le_abs_self _).trans ((Finset.single_le_sum (f := fun i => |si i|)
    (fun _ _ => abs_nonneg _) hmem).trans ((le_max_right _ _).trans hs))
  have hs0 : 0 ≤ s := (le_max_left _ _).trans hs
  have hη : Real.exp (-(b * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  calc ‖iteratedFDeriv ℝ i E (s, t)‖ ≤ Ci i * Real.exp (-(b * s)) := hCi i s hsi t
    _ ≤ |Ci i| * Real.exp (-(b * s)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    _ ≤ |Ci i| * 1 := mul_le_mul_of_nonneg_left hη (abs_nonneg _)
    _ = |Ci i| := mul_one _
    _ ≤ _ := Finset.single_le_sum (f := fun i => |Ci i|) (fun _ _ => abs_nonneg _) hmem

lemma cylInf_zero_zero : cylInf 0 0 = 1 := by
  rw [cylInf_eq_exp]; simp

lemma cylInf_eq_one {a b : ℝ} (h : cylInf a b = 1) (hb : |b| < 1) : a = 0 ∧ b = 0 := by
  have hn : ‖cylInf a b‖ = Real.exp (2 * π * a) := by
    unfold cylInf ccwLoop
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  rw [h, norm_one] at hn
  have ha : 2 * π * a = 0 := by
    have := Real.exp_eq_one_iff (2 * π * a) |>.1 hn.symm
    exact this
  have ha0 : a = 0 := by
    rcases mul_eq_zero.1 ha with h1 | h1
    · exact absurd h1 (by positivity)
    · exact h1
  refine ⟨ha0, ?_⟩
  rw [cylInf_eq_exp, ha0] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have him := congrArg Complex.im hn
  simp at him
  have hb' : b = n := by
    have hπ : (2 * π : ℝ) ≠ 0 := by positivity
    have : 2 * π * b = 2 * π * n := by linarith
    exact mul_left_cancel₀ hπ this
  have hn1 : |(n : ℝ)| < 1 := hb' ▸ hb
  have : n = 0 := by
    have := abs_lt.1 hn1
    have h1 : (-1 : ℤ) < n := by exact_mod_cast this.1
    have h2 : n < 1 := by exact_mod_cast this.2
    omega
  rw [hb', this]; simp

end BT

end

end FiniteEnergyPlane

/-! # B1, layer B: the inverse in log coordinates. -/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Nat Real

noncomputable section

namespace BT

/-- The shift `(log |κ|, arg κ) / (2π)`. -/
def kc (κ : ℂ) : ℝ × ℝ := (Real.log ‖κ‖ / (2 * π), Complex.arg κ / (2 * π))

lemma cylInf_kc {κ : ℂ} (hκ : κ ≠ 0) : cylInf (kc κ).1 (kc κ).2 = κ := cylInf_log_arg hκ

lemma cylInf_neg_kc {κ : ℂ} (hκ : κ ≠ 0) : cylInf (-(kc κ).1) (-(kc κ).2) = κ⁻¹ := by
  have h := cylInf_add (kc κ).1 (kc κ).2 (-(kc κ).1) (-(kc κ).2)
  rw [add_neg_cancel, add_neg_cancel, cylInf_zero_zero, cylInf_kc hκ] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

lemma contDiff_cylInf : ContDiff ℝ ∞ (fun q : ℝ × ℝ => cylInf q.1 q.2) := by
  have : (fun q : ℝ × ℝ => cylInf q.1 q.2) = fun q : ℝ × ℝ =>
      Complex.exp (((2 * π : ℝ) : ℂ) * ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)) :=
    funext fun q => cylInf_eq_exp q.1 q.2
  rw [this]
  refine Complex.contDiff_exp.comp (contDiff_const.mul ?_)
  exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).add
    ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)

lemma cylInf_add' (p q : ℝ × ℝ) : cylInf (p + q).1 (p + q).2 = cylInf p.1 p.2 * cylInf q.1 q.2 :=
  cylInf_add p.1 p.2 q.1 q.2

lemma norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- The normalized inverse `ψ⁻¹(z) κ / z - 1` is eventually small on the end. -/
lemma eventually_small_inv (ψ : ℂ ≃ₜ ℂ) (κ : ℂ) (hκ : κ ≠ 0) (b : ℝ) (hb : 0 < b)
    (E : ℝ × ℝ → ℝ × ℝ) (S₁ : ℝ) (hE : ExpDecayCInfty E b)
    (hrep : ∀ s ≥ S₁, ∀ t : ℝ,
      ψ (cylInf s t) = cylInf ((s, t) + kc κ + E (s, t)).1 ((s, t) + kc κ + E (s, t)).2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ s ≥ S, ∀ t : ℝ, ‖ψ.symm (cylInf s t) * κ / cylInf s t - 1‖ < ε := by
  -- continuity of `e ↦ cylInf (-c - e) * κ - 1` at `0`
  set G₀ : ℝ × ℝ → ℂ := fun e => cylInf (-(kc κ) - e).1 (-(kc κ) - e).2 * κ - 1 with hG₀
  have hG₀c : Continuous G₀ :=
    ((contDiff_cylInf.continuous.comp (continuous_const.sub continuous_id)).mul
      continuous_const).sub continuous_const
  have hG₀0 : G₀ 0 = 0 := by
    simp only [hG₀, sub_zero, Prod.fst_neg, Prod.snd_neg]
    rw [cylInf_neg_kc hκ, inv_mul_cancel₀ hκ, sub_self]
  obtain ⟨η, hη, hηG⟩ := Metric.continuous_iff.1 hG₀c 0 ε hε
  obtain ⟨S₃, hS₃⟩ := eventually_norm_lt hb hE hη
  set S₄ := max S₁ S₃ with hS₄
  set R := Real.exp (2 * π * S₄) with hR
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).image_of_continuousOn
    ψ.continuous.continuousOn |>.isBounded.exists_norm_le
  refine ⟨(Real.log (max M 1) + 1) / (2 * π), fun s hs t => ?_⟩
  set w := ψ.symm (cylInf s t) with hw
  have hπ : 0 < 2 * π := by positivity
  have hcs : max M 1 < ‖cylInf s t‖ := by
    rw [norm_cylInf]
    have h1 : Real.log (max M 1) + 1 ≤ 2 * π * s := by
      rw [ge_iff_le, div_le_iff₀ hπ] at hs; linarith
    calc max M 1 = Real.exp (Real.log (max M 1)) :=
          (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))).symm
      _ < Real.exp (2 * π * s) := Real.exp_lt_exp.2 (by linarith)
  have hwR : R < ‖w‖ := by
    by_contra hle
    push_neg at hle
    have := hM _ ⟨w, mem_closedBall_zero_iff.2 hle, rfl⟩
    rw [hw, ψ.apply_symm_apply] at this
    linarith [le_max_left M 1]
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hwR; exact absurd hwR (not_lt.2 (Real.exp_pos _).le)
  set p' : ℝ × ℝ := (Real.log ‖w‖ / (2 * π), Complex.arg w / (2 * π)) with hp'
  have hp'w : cylInf p'.1 p'.2 = w := cylInf_log_arg hw0
  have hp'1 : S₄ < p'.1 := by
    have : 2 * π * S₄ < Real.log ‖w‖ := by
      rw [← Real.exp_lt_exp, Real.exp_log (norm_pos_iff.2 hw0)]; exact hwR
    show S₄ < Real.log ‖w‖ / (2 * π)
    rw [lt_div_iff₀ hπ]; linarith
  have hrep' := hrep p'.1 ((le_max_left _ _).trans hp'1.le) p'.2
  rw [hp'w] at hrep'
  have hψw : ψ w = cylInf s t := ψ.apply_symm_apply _
  have hEp := hS₃ p'.1 ((le_max_right _ _).trans hp'1.le) p'.2
  have hkey : w * κ / cylInf s t - 1 = G₀ (E p') := by
    rw [← hψw, hrep']
    have hsplit : cylInf ((p'.1, p'.2) + kc κ + E (p'.1, p'.2)).1
        ((p'.1, p'.2) + kc κ + E (p'.1, p'.2)).2 =
        w * cylInf (kc κ + E p').1 (kc κ + E p').2 := by
      rw [← hp'w, ← cylInf_add']
      congr 1 <;> simp [add_assoc]
    have hinv : cylInf (-(kc κ) - E p').1 (-(kc κ) - E p').2 *
        cylInf (kc κ + E p').1 (kc κ + E p').2 = 1 := by
      rw [← cylInf_add']; simp [cylInf_zero_zero]
    have hne : cylInf (kc κ + E p').1 (kc κ + E p').2 ≠ 0 := cylInf_ne_zero _ _
    have hB := eq_inv_of_mul_eq_one_left hinv
    rw [hsplit]
    simp only [hG₀]
    rw [hB]
    field_simp
  rw [hkey]
  have := hηG (E p') (by rw [dist_zero_right]; exact hEp)
  rwa [hG₀0, dist_zero_right] at this

end BT

end

end FiniteEnergyPlane

/-! # B1, layer C: log coordinates of the inverse, `E' = -E ∘ Y`. -/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Nat Real

noncomputable section

namespace BT

/-- Log coordinates of `ψ⁻¹` on the end: `ψ⁻¹(cylInf q) = cylInf (q - kc κ + E' q)`, with `E'`
smooth and small, and `E' q = -E (q - kc κ + E' q)`. -/
lemma exists_inv_logCoords (ψ : ℂ ≃ₜ ℂ) (hψ' : ContDiff ℝ ∞ ψ.symm) (κ : ℂ) (hκ : κ ≠ 0)
    (b : ℝ) (hb : 0 < b) (E : ℝ × ℝ → ℝ × ℝ) (S₁ : ℝ) (hE : ExpDecayCInfty E b)
    (hrep : ∀ s ≥ S₁, ∀ t : ℝ,
      ψ (cylInf s t) = cylInf ((s, t) + kc κ + E (s, t)).1 ((s, t) + kc κ + E (s, t)).2)
    (T₀ : ℝ) :
    ∃ (E' : ℝ × ℝ → ℝ × ℝ) (S : ℝ), T₀ ≤ S ∧ ContDiffOn ℝ ∞ E' (Ioi S ×ˢ univ) ∧
      (∀ q : ℝ × ℝ, S ≤ q.1 → ‖E' q‖ ≤ 1 / 4) ∧
      (∀ q : ℝ × ℝ, S ≤ q.1 → T₀ ≤ (q - kc κ + E' q).1) ∧
      (∀ q : ℝ × ℝ, S ≤ q.1 → ψ.symm (cylInf q.1 q.2) =
        cylInf (q - kc κ + E' q).1 (q - kc κ + E' q).2) ∧
      ∀ q : ℝ × ℝ, S ≤ q.1 → E' q = -E (q - kc κ + E' q) := by
  -- the log chart is small near `0`
  have hcl : ContinuousAt (fun z : ℂ => reIm (lchart z)) 0 :=
    reIm.continuous.continuousAt.comp ((lchart_contDiffAt (by simp)).continuousAt)
  have hcl0 : reIm (lchart 0) = 0 := by rw [lchart_zero, map_zero]
  obtain ⟨η₁, hη₁, hη₁c⟩ := Metric.continuousAt_iff.1 hcl (1 / 4) (by norm_num)
  set η := min η₁ (1 / 2) with hη
  have hη0 : 0 < η := lt_min hη₁ (by norm_num)
  obtain ⟨S₂, hS₂⟩ := eventually_small_inv ψ κ hκ b hb E S₁ hE hrep hη0
  obtain ⟨S₃, hS₃⟩ := eventually_norm_lt hb hE (show (0 : ℝ) < 1 / 4 by norm_num)
  set S := max (max S₂ (S₁ + |(kc κ).1| + 1)) (max (S₃ + |(kc κ).1| + 1) (T₀ + |(kc κ).1| + 1))
    with hS
  have hSS₂ : S₂ ≤ S := (le_max_left _ _).trans (le_max_left _ _)
  have hSS₁ : S₁ + |(kc κ).1| + 1 ≤ S := (le_max_right _ _).trans (le_max_left _ _)
  have hSS₃ : S₃ + |(kc κ).1| + 1 ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  have hST : T₀ + |(kc κ).1| + 1 ≤ S := (le_max_right _ _).trans (le_max_right _ _)
  set ζ' : ℝ × ℝ → ℂ := fun q => ψ.symm (cylInf q.1 q.2) * κ / cylInf q.1 q.2 - 1 with hζ'
  set E' : ℝ × ℝ → ℝ × ℝ := fun q => reIm (lchart (ζ' q)) with hE'
  have hsm : ∀ q : ℝ × ℝ, S ≤ q.1 → ‖ζ' q‖ < η := fun q hq => hS₂ q.1 (hSS₂.trans hq) q.2
  have hsm1 : ∀ q : ℝ × ℝ, S ≤ q.1 → ‖ζ' q‖ < 1 := fun q hq =>
    (hsm q hq).trans_le ((min_le_right _ _).trans (by norm_num))
  have hE'small : ∀ q : ℝ × ℝ, S ≤ q.1 → ‖E' q‖ ≤ 1 / 4 := by
    intro q hq
    have := hη₁c (x := ζ' q) (by rw [dist_zero_right]; exact (hsm q hq).trans_le (min_le_left _ _))
    rw [hcl0, dist_zero_right] at this
    exact this.le
  have hfst : ∀ q : ℝ × ℝ, S ≤ q.1 → |(q - kc κ + E' q).1 - (q.1 - (kc κ).1)| ≤ 1 / 4 := by
    intro q hq
    have : (q - kc κ + E' q).1 - (q.1 - (kc κ).1) = (E' q).1 := by
      simp only [Prod.fst_add, Prod.fst_sub]; ring
    rw [this]
    exact (show |(E' q).1| ≤ ‖E' q‖ by rw [← Real.norm_eq_abs]; exact norm_fst_le _).trans
      (hE'small q hq)
  have hlow : ∀ q : ℝ × ℝ, S ≤ q.1 → ∀ T : ℝ, T + |(kc κ).1| + 1 ≤ S →
      T ≤ (q - kc κ + E' q).1 := by
    intro q hq T hT
    have h1 := (abs_le.1 (hfst q hq)).1
    have h2 := le_abs_self (kc κ).1
    linarith
  -- smoothness
  have hU : IsOpen (Ioi S ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hζs : ContDiffOn ℝ ∞ ζ' (Ioi S ×ˢ univ) := by
    have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ => ψ.symm (cylInf q.1 q.2) * κ) :=
      (hψ'.comp contDiff_cylInf).mul contDiff_const
    have hic : ContDiff ℝ ∞ (fun q : ℝ × ℝ => (cylInf q.1 q.2)⁻¹) :=
      contDiff_iff_contDiffAt.2 fun q =>
        (contDiffAt_inv ℝ (cylInf_ne_zero q.1 q.2)).comp q contDiff_cylInf.contDiffAt
    exact ((h1.mul hic).sub (contDiff_const (c := (1 : ℂ)))).contDiffOn.congr fun q _ => by
      simp only [hζ', div_eq_mul_inv]
  have hE's : ContDiffOn ℝ ∞ E' (Ioi S ×ˢ univ) :=
    reIm.contDiff.comp_contDiffOn (lchart_contDiffOn.comp hζs fun q hq =>
      mem_ball_zero_iff.2 (hsm1 q (le_of_lt hq.1)))
  -- the representation of `ψ⁻¹`
  have hinv : ∀ q : ℝ × ℝ, S ≤ q.1 → ψ.symm (cylInf q.1 q.2) =
      cylInf (q - kc κ + E' q).1 (q - kc κ + E' q).2 := by
    intro q hq
    have hc := cylInf_ne_zero q.1 q.2
    have h1 : ψ.symm (cylInf q.1 q.2) = cylInf q.1 q.2 * κ⁻¹ * (1 + ζ' q) := by
      simp only [hζ']
      field_simp
      ring
    have h2 : cylInf (q - kc κ).1 (q - kc κ).2 = cylInf q.1 q.2 * κ⁻¹ := by
      rw [sub_eq_add_neg, cylInf_add', ← cylInf_neg_kc hκ]; rfl
    rw [h1, ← h2, cylInf_mul_one_add _ _ (hsm1 q hq)]
    simp only [hE', reIm_apply, Prod.fst_add, Prod.snd_add]
  refine ⟨E', S, ?_, hE's, hE'small, fun q hq => hlow q hq T₀ hST, hinv, fun q hq => ?_⟩
  · have := le_abs_self (kc κ).1
    have := abs_nonneg (kc κ).1
    linarith
  -- `E' = -E ∘ Y`
  set Y := q - kc κ + E' q with hY
  have hY1 : S₁ ≤ Y.1 := hlow q hq S₁ hSS₁
  have hY3 : S₃ ≤ Y.1 := hlow q hq S₃ hSS₃
  have h1 : cylInf q.1 q.2 = ψ (cylInf Y.1 Y.2) := by
    rw [← hinv q hq, ψ.apply_symm_apply]
  have h2 := hrep Y.1 hY1 Y.2
  rw [← h1] at h2
  set d : ℝ × ℝ := E' q + E Y with hd
  have h3 : (Y.1, Y.2) + kc κ + E (Y.1, Y.2) = q + d := by
    simp only [hY, hd, Prod.mk.eta]; abel
  rw [h3, cylInf_add'] at h2
  have h4 : cylInf d.1 d.2 = 1 := by
    have hc := cylInf_ne_zero q.1 q.2
    exact (mul_eq_left₀ hc).1 h2.symm
  have hd2 : |d.2| < 1 := by
    have e1 : |d.2| ≤ ‖d‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le _
    have e2 : ‖d‖ ≤ ‖E' q‖ + ‖E Y‖ := norm_add_le _ _
    have e3 := hE'small q hq
    have e4 : ‖E Y‖ < 1 / 4 := hS₃ Y.1 hY3 Y.2
    linarith
  obtain ⟨hd1, hd2'⟩ := cylInf_eq_one h4 hd2
  have : d = 0 := Prod.ext hd1 hd2'
  rw [hd] at this
  exact eq_neg_of_add_eq_zero_left this

end BT

end

end FiniteEnergyPlane

/-! # B1, layer D: derivative bounds and decay of the inverse log coordinates; B1. -/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Nat Real

noncomputable section

namespace BT

abbrev L2 := ℝ × ℝ →L[ℝ] ℝ × ℝ

/-- `A ↦ -(1 + A)⁻¹ A`. -/
def invPhi (A : L2) : L2 := -(Ring.inverse (1 + A) * A)

lemma isUnit_one_add {A : L2} (hA : ‖A‖ < 1) : IsUnit (1 + A) := by
  have h : ‖-A‖ < 1 := by rwa [norm_neg]
  have := (Units.oneSub (-A) h).isUnit
  simpa [Units.oneSub, sub_neg_eq_add] using this

lemma invPhi_contDiffOn : ContDiffOn ℝ ∞ invPhi (ball (0 : L2) 1) := by
  intro A hA
  have hA' : ‖A‖ < 1 := mem_ball_zero_iff.1 hA
  obtain ⟨u, hu⟩ := isUnit_one_add hA'
  have h1 : ContDiffAt ℝ ∞ (fun B : L2 => Ring.inverse (1 + B)) A := by
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) u
    rw [hu] at this
    exact this.comp A (contDiffAt_const.add contDiffAt_id)
  exact ((h1.mul contDiffAt_id).neg).contDiffWithinAt

lemma invPhi_zero : invPhi 0 = 0 := by simp [invPhi]

lemma invPhi_eq {A B : L2} (hA : ‖A‖ < 1) (h : B = -(A * (1 + B))) : B = invPhi A := by
  have hu := isUnit_one_add hA
  have h2 : (1 + A) * B = -A := by
    rw [add_mul, one_mul]
    nth_rewrite 1 [h]
    noncomm_ring
  unfold invPhi
  calc B = Ring.inverse (1 + A) * ((1 + A) * B) := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
    _ = -(Ring.inverse (1 + A) * A) := by rw [h2]; exact ContinuousLinearMap.ext fun x => by simp [ContinuousLinearMap.mul_apply]

end BT

end

end FiniteEnergyPlane

/-! # B1: asymptotics of the inverse. -/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Nat Real

noncomputable section

namespace BT

lemma norm_iteratedFDeriv_add_const_le' (c x : ℝ × ℝ) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun p : ℝ × ℝ => p + c) x‖ ≤ 1 := by
  have e : (fun p : ℝ × ℝ => p + c) = fun p => (id : ℝ × ℝ → ℝ × ℝ) (p + c) := rfl
  rw [e, iteratedFDeriv_comp_add_right]
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hid : fderiv ℝ (id : ℝ × ℝ → ℝ × ℝ) = fun _ => ContinuousLinearMap.id ℝ (ℝ × ℝ) :=
    funext fun y => fderiv_id
  rw [← norm_iteratedFDeriv_fderiv, hid]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [norm_iteratedFDeriv_zero]
    exact ContinuousLinearMap.norm_id_le
  · rw [iteratedFDeriv_const_of_ne hj.ne']
    simp

lemma norm_iteratedFDeriv_shift_add_le {E' : ℝ × ℝ → ℝ × ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hE' : ContDiffOn ℝ ∞ E' U) (c : ℝ × ℝ) {q : ℝ × ℝ} (hq : q ∈ U) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun y => y + c + E' y) q‖ ≤ 1 + ‖iteratedFDeriv ℝ i E' q‖ := by
  have hca : ContDiffAt ℝ i (fun p : ℝ × ℝ => p + c) q :=
    (contDiff_id.add contDiff_const).contDiffAt
  have hEa : ContDiffAt ℝ i E' q :=
    (hE'.contDiffAt (hU.mem_nhds hq)).of_le (by exact_mod_cast le_top)
  have e : (fun y => y + c + E' y) = (fun p : ℝ × ℝ => p + c) + E' := rfl
  rw [e, iteratedFDeriv_add_apply hca hEa]
  exact (norm_add_le _ _).trans (by linarith [norm_iteratedFDeriv_add_const_le' c q hi])

end BT

open BT in
theorem expDecayCInfty_symm_div_sub_aux (ψ : ℂ ≃ₜ ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hψ' : ContDiff ℝ ∞ ψ.symm) (κ : ℂ) (hκ : κ ≠ 0) (b : ℝ) (hb : 0 < b)
    (has : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b) :
    ExpDecayCInfty (fun p : ℝ × ℝ => ψ.symm (cylInf p.1 p.2) / cylInf p.1 p.2 - κ⁻¹) b := by
  obtain ⟨E, S₁, hE, hrep⟩ := exists_logCoords_of_div_sub ψ κ hκ b hb has
  have hrep' : ∀ s ≥ S₁, ∀ t : ℝ,
      ψ (cylInf s t) = cylInf ((s, t) + kc κ + E (s, t)).1 ((s, t) + kc κ + E (s, t)).2 := hrep
  have hDE := expDecay_fderiv hE
  set M : ℝ × ℝ → L2 := fun p => invPhi (fderiv ℝ E p) with hMdef
  have hM : ExpDecayCInfty M b :=
    expDecayCInfty_comp_left invPhi 1 one_pos invPhi_contDiffOn invPhi_zero _ b hb hDE
  obtain ⟨rE, hEs⟩ := hE.1
  obtain ⟨rM, hMs⟩ := hM.1
  obtain ⟨T₁, hT₁⟩ := eventually_norm_lt hb hDE one_pos
  set T₀ := max (max (rE + 1) (rM + 1)) T₁ with hT₀
  obtain ⟨E', S, hST, hE's, hE'sm, hYlow, hinv, hfix⟩ :=
    exists_inv_logCoords ψ hψ' κ hκ b hb E S₁ hE hrep' T₀
  set Y : ℝ × ℝ → ℝ × ℝ := fun q => q + (-kc κ) + E' q with hYdef
  have hYeq : ∀ q, q - kc κ + E' q = Y q := fun q => by simp only [hYdef, sub_eq_add_neg]
  set U : Set (ℝ × ℝ) := Ioi S ×ˢ univ with hU
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hYs : ContDiffOn ℝ ∞ Y U := ((contDiff_id.add contDiff_const).contDiffOn).add hE's
  have hYT : ∀ q ∈ U, T₀ ≤ (Y q).1 := fun q hq => by
    rw [← hYeq]; exact hYlow q (le_of_lt hq.1)
  have hYmapsE : MapsTo Y U (Ioi rE ×ˢ univ) := fun q hq =>
    ⟨by have := hYT q hq; have := le_max_left (max (rE + 1) (rM + 1)) T₁
        have := le_max_left (rE + 1) (rM + 1); show rE < (Y q).1; linarith, trivial⟩
  have hYmapsM : MapsTo Y U (Ioi rM ×ˢ univ) := fun q hq =>
    ⟨by have := hYT q hq; have := le_max_left (max (rE + 1) (rM + 1)) T₁
        have := le_max_right (rE + 1) (rM + 1); show rM < (Y q).1; linarith, trivial⟩
  have hVE : IsOpen (Ioi rE ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hVM : IsOpen (Ioi rM ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hfixU : EqOn E' (fun q => -E (Y q)) U := fun q hq => by
    simp only; rw [← hYeq]; exact hfix q (le_of_lt hq.1)
  -- the derivative of `E'`
  have hder : ∀ q ∈ U, fderiv ℝ E' q = M (Y q) := by
    intro q hq
    have hE'd : HasFDerivAt E' (fderiv ℝ E' q) q :=
      ((hE's.contDiffAt (hUo.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
    have hYd : HasFDerivAt Y (ContinuousLinearMap.id ℝ (ℝ × ℝ) + fderiv ℝ E' q) q :=
      ((hasFDerivAt_id q).add_const (-kc κ)).add hE'd
    have hEd : HasFDerivAt E (fderiv ℝ E (Y q)) (Y q) :=
      ((hEs.contDiffAt (hVE.mem_nhds (hYmapsE hq))).differentiableAt (by simp)).hasFDerivAt
    have hcomp := (hEd.comp q hYd).neg
    have hE'2 : HasFDerivAt E' (-(fderiv ℝ E (Y q)).comp
        (ContinuousLinearMap.id ℝ (ℝ × ℝ) + fderiv ℝ E' q)) q :=
      hcomp.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hUo.mem_nhds hq) hfixU)
    have hB := hE'd.unique hE'2
    have hsmall : ‖fderiv ℝ E (Y q)‖ < 1 := by
      have := hT₁ (Y q).1 ((le_max_right _ _).trans (hYT q hq)) (Y q).2
      simpa using this
    refine invPhi_eq hsmall ?_
    conv_lhs => rw [hB]
    exact ContinuousLinearMap.ext fun x => by simp [ContinuousLinearMap.mul_apply]
  -- bounded derivatives of `E'`
  have hbd : ∀ k : ℕ, ∃ B T : ℝ, 0 ≤ B ∧ S ≤ T ∧
      ∀ i ≤ k, ∀ q : ℝ × ℝ, T ≤ q.1 → ‖iteratedFDeriv ℝ i E' q‖ ≤ B := by
    intro k
    induction k with
    | zero =>
      refine ⟨1 / 4, S, by norm_num, le_rfl, fun i hi q hq => ?_⟩
      obtain rfl : i = 0 := by omega
      rw [norm_iteratedFDeriv_zero]; exact hE'sm q hq
    | succ k ih =>
      obtain ⟨B, T, hB0, hST', hbB⟩ := ih
      obtain ⟨CM, TM, hCM0, hCM⟩ := bound_of_expDecay hb.le hM k
      set T' := max (T + 1) (TM + |(kc κ).1| + 1) with hT'
      refine ⟨max B (k ! * CM * (1 + B) ^ k), T', le_max_of_le_left hB0,
        hST'.trans (by linarith [le_max_left (T + 1) (TM + |(kc κ).1| + 1)]), fun i hi q hq => ?_⟩
      have hqT : T ≤ q.1 := by linarith [hT', le_max_left (T + 1) (TM + |(kc κ).1| + 1)]
      rcases Nat.lt_or_ge i (k + 1) with hik | hik
      · exact (hbB i (by omega) q hqT).trans (le_max_left _ _)
      obtain rfl : i = k + 1 := by omega
      have hqU : q ∈ U := ⟨show S < q.1 by linarith [hT', le_max_left (T + 1) (TM + |(kc κ).1| + 1)], trivial⟩
      have hY1 : TM ≤ (Y q).1 := by
        have h1 := hE'sm q (by linarith)
        have h2 : |(E' q).1| ≤ ‖E' q‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le _
        have h3 := (abs_le.1 (h2.trans h1)).1
        have h4 := le_abs_self (kc κ).1
        have h5 := le_max_right (T + 1) (TM + |(kc κ).1| + 1)
        have h6 : (Y q).1 = q.1 + -(kc κ).1 + (E' q).1 := rfl
        linarith [hT']
      rw [← norm_iteratedFDeriv_fderiv,
        iteratedFDeriv_congr_open hUo (fun y hy => hder y hy) hqU k]
      refine (fdb hUo hVM hMs hYs hYmapsM hqU (k := k) (C := CM) (D := 1 + B)
        (fun j hj => ?_) (fun j hj1 hj => ?_)).trans (le_max_right _ _)
      · have := hCM j hj (Y q).1 hY1 (Y q).2
        simpa using this
      · calc ‖iteratedFDeriv ℝ j Y q‖ ≤ 1 + ‖iteratedFDeriv ℝ j E' q‖ :=
            norm_iteratedFDeriv_shift_add_le hUo hE's (-kc κ) hqU hj1
          _ ≤ 1 + B := by linarith [hbB j (by omega) q hqT]
          _ ≤ (1 + B) ^ j := le_self_pow₀ (by linarith) (by omega)
  -- decay of `E'`
  have hE'dec : ExpDecayCInfty E' b := by
    refine ⟨⟨S, hE's⟩, fun m => ?_⟩
    obtain ⟨B, T, hB0, hST', hbB⟩ := hbd m
    choose Ci si hCi using hE.2
    set C' : ℝ := ∑ i ∈ Finset.range (m + 1), |Ci i| with hC'
    set Tm : ℝ := ∑ i ∈ Finset.range (m + 1), |si i| with hTm
    set K : ℝ := Real.exp (b * (|(kc κ).1| + 1)) with hK
    refine ⟨m ! * (C' * K) * (1 + B) ^ m, max (T + 1) (Tm + |(kc κ).1| + 1), fun s hs t => ?_⟩
    have hsT : T ≤ s := by linarith [le_max_left (T + 1) (Tm + |(kc κ).1| + 1)]
    have hqU : (s, t) ∈ U :=
      ⟨show S < s by linarith [le_max_left (T + 1) (Tm + |(kc κ).1| + 1)], trivial⟩
    have hYlo : s - |(kc κ).1| - 1 / 4 ≤ (Y (s, t)).1 := by
      have h1 := hE'sm (s, t) (by simp; linarith)
      have h2 : |(E' (s, t)).1| ≤ ‖E' (s, t)‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le _
      have h3 := (abs_le.1 (h2.trans h1)).1
      have h4 := le_abs_self (kc κ).1
      have h6 : (Y (s, t)).1 = s + -(kc κ).1 + (E' (s, t)).1 := rfl
      linarith
    rw [iteratedFDeriv_congr_open hUo hfixU hqU m]
    have hfd := fdb hUo hVE hEs.neg hYs hYmapsE hqU (k := m)
      (C := C' * K * Real.exp (-(b * s))) (D := 1 + B) (fun j hj => ?_) (fun j hj1 hj => ?_)
    · calc _ ≤ _ := hfd
        _ = m ! * (C' * K) * (1 + B) ^ m * Real.exp (-(b * s)) := by ring
    · have hneg : (fun y => -E y) = -E := rfl
      rw [hneg, iteratedFDeriv_neg_apply, norm_neg]
      have hmem : j ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
      have hsj : si j ≤ (Y (s, t)).1 := by
        have := (le_abs_self (si j)).trans (Finset.single_le_sum (f := fun i => |si i|)
          (fun _ _ => abs_nonneg _) hmem)
        have := le_max_right (T + 1) (Tm + |(kc κ).1| + 1)
        linarith
      have hCj : Ci j ≤ C' := (le_abs_self _).trans (Finset.single_le_sum
        (f := fun i => |Ci i|) (fun _ _ => abs_nonneg _) hmem)
      have hC'0 : 0 ≤ C' := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hex : Real.exp (-(b * (Y (s, t)).1)) ≤ K * Real.exp (-(b * s)) := by
        rw [hK, ← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith
      calc ‖iteratedFDeriv ℝ j E (Y (s, t))‖
          = ‖iteratedFDeriv ℝ j E ((Y (s, t)).1, (Y (s, t)).2)‖ := rfl
        _ ≤ Ci j * Real.exp (-(b * (Y (s, t)).1)) := hCi j _ hsj _
        _ ≤ C' * Real.exp (-(b * (Y (s, t)).1)) :=
            mul_le_mul_of_nonneg_right hCj (Real.exp_pos _).le
        _ ≤ C' * (K * Real.exp (-(b * s))) := mul_le_mul_of_nonneg_left hex hC'0
        _ = C' * K * Real.exp (-(b * s)) := by ring
    · calc ‖iteratedFDeriv ℝ j Y (s, t)‖ ≤ 1 + ‖iteratedFDeriv ℝ j E' (s, t)‖ :=
          norm_iteratedFDeriv_shift_add_le hUo hE's (-kc κ) hqU hj1
        _ ≤ 1 + B := by linarith [hbB j (by omega) (s, t) hsT]
        _ ≤ (1 + B) ^ j := le_self_pow₀ (by linarith) (by omega)
  -- the target
  set G : ℝ × ℝ → ℂ := fun e => κ⁻¹ * (cylInf e.1 e.2 - 1) with hG
  have hGs : ContDiff ℝ ∞ G := contDiff_const.mul (contDiff_cylInf.sub contDiff_const)
  have hG0 : G 0 = 0 := by simp [hG, cylInf_zero_zero]
  have hdec := expDecayCInfty_comp_left G 1 one_pos hGs.contDiffOn hG0 E' b hb hE'dec
  refine expDecayCInfty_congr hdec (s₀ := S) fun s hs t => ?_
  have h1 := hinv (s, t) hs.le
  simp only at h1 ⊢
  rw [h1, hYeq, hG]
  have h2 : cylInf (Y (s, t)).1 (Y (s, t)).2 =
      cylInf s t * cylInf (-kc κ).1 (-kc κ).2 * cylInf (E' (s, t)).1 (E' (s, t)).2 := by
    show cylInf ((s, t) + -kc κ + E' (s, t)).1 ((s, t) + -kc κ + E' (s, t)).2 = _
    rw [cylInf_add', cylInf_add']
  have h3 : cylInf (-kc κ).1 (-kc κ).2 = κ⁻¹ := by
    simpa using cylInf_neg_kc hκ
  rw [h2, h3]
  have hc := cylInf_ne_zero s t
  field_simp

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff Real

theorem solution (ψ : ℂ ≃ₜ ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hψ' : ContDiff ℝ ∞ ψ.symm) (κ : ℂ) (hκ : κ ≠ 0) (b : ℝ) (hb : 0 < b)
    (has : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b) :
    ExpDecayCInfty (fun p : ℝ × ℝ => ψ.symm (cylInf p.1 p.2) / cylInf p.1 p.2 - κ⁻¹) b :=
  expDecayCInfty_symm_div_sub_aux ψ hψ hψ' κ hκ b hb has
