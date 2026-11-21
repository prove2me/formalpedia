-- Prove2me | solution 1 for FiniteEnergyPlane.GraphEnd.isExpAsymptoticTo_Sf
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T15:35:04.506592+00:00
-- url     : https://prove2.me/submissions/98ecbc7c-6771-4f54-bf41-157b1b1498ec

import Definitions.Def_FiniteEnergyPlane_GraphEnd
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_comp_left
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_congr
import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_hadamard_integral_fderiv
import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_of_tendstoZeroCInfty
import Theorems.Thm_FiniteEnergyPlane_norm_iteratedFDeriv_intervalIntegral_le
import Theorems.Thm_FiniteEnergyPlane_cylJ_iteratedFDeriv_bdd
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_comp_of_div_sub
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_mono
import Theorems.Thm_ContWeatherall_contDiff_parametric_intervalIntegral
import Theorems.Thm_FiniteEnergyPlane_exists_logCoords_of_div_sub
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_comp_shift



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

/-! B3E layer A: block algebra of a real-linear structure on `ℂ × ℂ` and the frame `qL`. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open ContinuousLinearMap

noncomputable section


lemma apply_fst (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) (e w : ℂ) : (J (e, w)).1 = J11 J e + J12 J w := by
  have : ((e, w) : ℂ × ℂ) = inl ℝ ℂ ℂ e + inr ℝ ℂ ℂ w := by simp
  rw [this, map_add]; rfl

lemma apply_snd (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) (e w : ℂ) : (J (e, w)).2 = J21 J e + J22 J w := by
  have : ((e, w) : ℂ × ℂ) = inl ℝ ℂ ℂ e + inr ℝ ℂ ℂ w := by simp
  rw [this, map_add]; rfl



lemma Ablk_eq_zero (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) (G : ℂ →L[ℝ] ℂ)
    (h : ∀ e : ℂ, (J (e, G e)).2 = G (J (e, G e)).1) : Ablk J G = 0 := by
  ext1 e
  have := h e
  rw [apply_fst, apply_snd, map_add] at this
  simp only [Ablk, sub_apply, add_apply, comp_apply, zero_apply]
  linear_combination this

lemma Bblk_sq (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) (G : ℂ →L[ℝ] ℂ) (hJ : J.comp J = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (hA : Ablk J G = 0) (x : ℂ) : Bblk J G (Bblk J G x) = -x := by
  have hsq : ∀ e w : ℂ, J (J (e, w)) = (-e, -w) := by
    intro e w
    have := congrArg (fun L : ℂ × ℂ →L[ℝ] ℂ × ℂ => L (e, w)) hJ
    simpa using this
  -- block identities of `J² = -1`
  have h22 : ∀ w, J21 J (J12 J w) + J22 J (J22 J w) = -w := by
    intro w
    have := congrArg Prod.snd (hsq 0 w)
    rw [← Prod.mk.eta (p := J (0, w)), apply_snd, apply_fst, apply_snd] at this
    simpa using this
  have h12 : ∀ w, J11 J (J12 J w) + J12 J (J22 J w) = 0 := by
    intro w
    have := congrArg Prod.fst (hsq 0 w)
    rw [← Prod.mk.eta (p := J (0, w)), apply_fst, apply_fst, apply_snd] at this
    simpa using this
  have hA' : ∀ e, J21 J e = G (J11 J e) - J22 J (G e) + G (J12 J (G e)) := by
    intro e
    have := congrArg (fun L : ℂ →L[ℝ] ℂ => L e) hA
    simp only [Ablk, sub_apply, add_apply, comp_apply, zero_apply] at this
    linear_combination this
  simp only [Bblk, sub_apply, comp_apply, map_sub]
  have e1 := h22 x
  rw [hA'] at e1
  have e2 := h12 x
  have e3 := congrArg G e2
  rw [map_add, map_zero] at e3
  linear_combination e1 - e3

/-- If `z ↦ (ψ z, v z)` has derivative `(Dψ, Dv)` intertwining `i` with `J`, then the difference
`Dh = Dv - G Dψ` satisfies `Dh (i e) = Ablk (Dψ e) + Bblk (Dh e)`. -/
lemma dh_I (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) (G Dψ Dv : ℂ →L[ℝ] ℂ)
    (hhol : ∀ e : ℂ, (Dψ (Complex.I * e), Dv (Complex.I * e)) = J (Dψ e, Dv e)) (e : ℂ) :
    (Dv - G.comp Dψ) (Complex.I * e) =
      Ablk J G (Dψ e) + Bblk J G ((Dv - G.comp Dψ) e) := by
  have h1 := congrArg Prod.fst (hhol e)
  have h2 := congrArg Prod.snd (hhol e)
  simp only at h1 h2
  rw [apply_fst] at h1; rw [apply_snd] at h2
  simp only [Ablk, Bblk, sub_apply, add_apply, comp_apply, map_sub, map_add, h1, h2]
  abel

/-! ### The frame `qL c`: `ℂ`-coordinates for the complex structure with `C 1 = c` -/



lemma qinvL_apply (c u : ℂ) : qinvL c u = u.re + u.im * c := by
  simp [qinvL, mul_comm]

lemma qL_apply (c u : ℂ) : qL c u = u.re + u.im * ((Complex.I - c.re) / c.im) := by
  simp [qL, mul_comm]

lemma qinvL_qL (c : ℂ) (hc : c.im ≠ 0) (u : ℂ) : qinvL c (qL c u) = u := by
  rw [qinvL_apply, qL_apply]
  apply Complex.ext <;> simp <;> field_simp <;> ring

lemma qL_qinvL (c : ℂ) (hc : c.im ≠ 0) (u : ℂ) : qL c (qinvL c u) = u := by
  rw [qinvL_apply, qL_apply]
  apply Complex.ext <;> simp <;> field_simp <;> ring

lemma qL_injective (c : ℂ) (hc : c.im ≠ 0) : Function.Injective (qL c) :=
  fun u u' h => by rw [← qinvL_qL c hc u, h, qinvL_qL c hc]

/-- A real-linear `C` with `C² = -1` has `(C 1).im ≠ 0`. -/
lemma im_ne_zero_of_sq (C : ℂ →L[ℝ] ℂ) (hC : ∀ x, C (C x) = -x) : (C 1).im ≠ 0 := by
  intro h
  have hr : C 1 = ((C 1).re : ℂ) := by apply Complex.ext <;> simp [h]
  have := hC 1
  rw [hr] at this
  have h2 : C (((C 1).re : ℝ) • (1 : ℂ)) = (C 1).re • C 1 := map_smul C _ _
  simp only [Complex.real_smul, mul_one] at h2
  rw [h2, hr] at this
  have := congrArg Complex.re this
  simp at this
  nlinarith [sq_nonneg (C 1).re]

/-- `qL (C 1)` intertwines `C` with multiplication by `i`. -/
lemma qL_intertwine (C : ℂ →L[ℝ] ℂ) (hC : ∀ x, C (C x) = -x) (x : ℂ) :
    qL (C 1) (C x) = Complex.I * qL (C 1) x := by
  have hc := im_ne_zero_of_sq C hC
  set c := C 1
  -- `qinvL c (i u) = C (qinvL c u)`
  have key : ∀ u, qinvL c (Complex.I * u) = C (qinvL c u) := by
    intro u
    rw [qinvL_apply, qinvL_apply]
    have hlin : C ((u.re : ℂ) + (u.im : ℂ) * c) = u.re • c + u.im • C c := by
      rw [map_add]
      congr 1
      · have : ((u.re : ℂ)) = (u.re : ℝ) • (1 : ℂ) := by simp
        rw [this, map_smul]
      · have : ((u.im : ℂ) * c) = (u.im : ℝ) • c := by simp
        rw [this, map_smul]
    rw [hlin, hC 1]
    simp only [Complex.real_smul]
    apply Complex.ext <;> simp <;> ring
  obtain ⟨u, rfl⟩ : ∃ u, qinvL c u = x := ⟨qL c x, qinvL_qL c hc x⟩
  rw [← key, qL_qinvL c hc, qL_qinvL c hc]

end

end FiniteEnergyPlane.B3E

/-! B3E layer P: retraction, Hadamard coefficients, the frame `Pf` and the plane identity. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap
open scoped ContDiff Real

noncomputable section

/-! ### A uniform bound strictly inside the ball -/

lemma exists_norm_le_of_expDecay (f : ℂ → ℂ) (hf : Continuous f) (ρ : ℝ)
    (hfρ : ∀ x, f x ∈ ball (0 : ℂ) ρ) (δ : ℝ) (hδ : δ < 0)
    (has : ExpDecayCInfty (fun p : ℝ × ℝ => f (cylInf p.1 p.2)) (-δ)) :
    ∃ r₁ : ℝ, 0 ≤ r₁ ∧ r₁ < ρ ∧ ∀ x, ‖f x‖ ≤ r₁ := by
  have hρ : 0 < ρ := by
    have := hfρ 0; rw [mem_ball_zero_iff] at this; exact (norm_nonneg _).trans_lt this
  obtain ⟨C, s₁, hC⟩ := has.2 0
  have ht : Tendsto (fun s : ℝ => C * Real.exp (δ * s)) atTop (𝓝 0) := by
    have : Tendsto (fun s : ℝ => Real.exp (δ * s)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hδ)
    simpa using this.const_mul C
  obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 ((ht.eventually (gt_mem_nhds (half_pos hρ))).and
    (eventually_ge_atTop s₁))
  set R := Real.exp (2 * π * s₂)
  obtain ⟨z₀, -, hz₀⟩ := (isCompact_closedBall (0 : ℂ) R).exists_isMaxOn
    (nonempty_closedBall.2 (Real.exp_pos _).le) (hf.norm.continuousOn)
  refine ⟨max (ρ / 2) ‖f z₀‖, le_max_of_le_left (by positivity),
    max_lt (half_lt_self hρ) (mem_ball_zero_iff.1 (hfρ z₀)), fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ R
  · exact le_max_of_le_right (hz₀ (mem_closedBall_zero_iff.2 hx))
  · push_neg at hx
    have hx0 : x ≠ 0 := by
      intro h; rw [h, norm_zero] at hx; exact absurd hx (not_lt.2 (Real.exp_pos _).le)
    have hs : s₂ < Real.log ‖x‖ / (2 * π) := by
      rw [lt_div_iff₀ (by positivity), mul_comm, ← Real.lt_log_iff_exp_lt (norm_pos_iff.2 hx0)]
        at *
      exact hx
    have hb := hC _ ((hs₂ _ hs.le).2) (Complex.arg x / (2 * π))
    rw [norm_iteratedFDeriv_zero] at hb
    simp only [BT.cylInf_log_arg hx0] at hb
    refine le_max_of_le_left (hb.trans ?_)
    have := (hs₂ _ hs.le).1
    rw [neg_mul, neg_neg] at *
    exact this.le

/-! ### The retraction -/


lemma rtr_contDiff (β : ContDiffBump (0 : ℂ)) : ContDiff ℝ ∞ (rtr β) :=
  β.contDiff.smul contDiff_id

lemma rtr_eq (β : ContDiffBump (0 : ℂ)) {w : ℂ} (hw : ‖w‖ ≤ β.rIn) : rtr β w = w := by
  simp [rtr, β.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hw)]

lemma rtr_mem (β : ContDiffBump (0 : ℂ)) (w : ℂ) : ‖rtr β w‖ < β.rOut := by
  by_cases h : β w = 0
  · simp [rtr, h, β.rOut_pos]
  · have hw : w ∈ ball (0 : ℂ) β.rOut := by
      rw [← β.support_eq]; exact h
    rw [mem_ball_zero_iff] at hw
    calc ‖rtr β w‖ = |β w| * ‖w‖ := by simp [rtr, norm_smul]
      _ ≤ 1 * ‖w‖ := by
          gcongr; rw [abs_of_nonneg β.nonneg]; exact β.le_one
      _ < β.rOut := by simpa using hw

/-! ### Re-centred blocks and their Hadamard coefficients -/

variable (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (β : ContDiffBump (0 : ℂ)) (g : ℂ → ℂ)







lemma contDiff_blocks :
    ContDiff ℝ ∞ (fun J : ℂ × ℂ →L[ℝ] ℂ × ℂ => J11 J) ∧
    ContDiff ℝ ∞ (fun J : ℂ × ℂ →L[ℝ] ℂ × ℂ => J12 J) ∧
    ContDiff ℝ ∞ (fun J : ℂ × ℂ →L[ℝ] ℂ × ℂ => J21 J) ∧
    ContDiff ℝ ∞ (fun J : ℂ × ℂ →L[ℝ] ℂ × ℂ => J22 J) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · exact contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

variable {Jbar β g}

lemma Jt_contDiff {ρ : ℝ} (hJ : ContDiffOn ℝ ∞ Jbar (univ ×ˢ ball (0 : ℂ) ρ))
    (hβ : β.rOut ≤ ρ) : ContDiff ℝ ∞ (Jt Jbar β) := by
  refine hJ.comp_contDiff (contDiff_fst.prodMk ((rtr_contDiff β).comp contDiff_snd)) ?_
  intro p
  exact ⟨mem_univ _, mem_ball_zero_iff.2 ((rtr_mem β p.2).trans_le hβ)⟩

lemma Afun_Bfun_contDiff {ρ : ℝ} (hJ : ContDiffOn ℝ ∞ Jbar (univ ×ˢ ball (0 : ℂ) ρ))
    (hβ : β.rOut ≤ ρ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (Afun Jbar β g) ∧ ContDiff ℝ ∞ (Bfun Jbar β g) := by
  have hJt : ContDiff ℝ ∞ (fun p : ℂ × ℂ => Jt Jbar β (p.1, g p.1 + p.2)) :=
    (Jt_contDiff hJ hβ).comp (contDiff_fst.prodMk ((hg.comp contDiff_fst).add contDiff_snd))
  have hG : ContDiff ℝ ∞ (fun p : ℂ × ℂ => fderiv ℝ g p.1) :=
    (hg.fderiv_right (m := ∞) (by simp)).comp contDiff_fst
  obtain ⟨h11, h12, h21, h22⟩ := contDiff_blocks
  have b11 := h11.comp hJt
  have b12 := h12.comp hJt
  have b21 := h21.comp hJt
  have b22 := h22.comp hJt
  constructor
  · exact ((b21.sub (hG.clm_comp b11)).add (b22.clm_comp hG)).sub (hG.clm_comp (b12.clm_comp hG))
  · exact b22.sub (hG.clm_comp b12)

lemma hadamard_A {ρ : ℝ} (hJ : ContDiffOn ℝ ∞ Jbar (univ ×ˢ ball (0 : ℂ) ρ))
    (hβ : β.rOut ≤ ρ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (KA Jbar β g) ∧ ∀ p, Afun Jbar β g p = Afun Jbar β g (p.1, 0) + KA Jbar β g p p.2 :=
  hadamard_integral_fderiv _ (Afun_Bfun_contDiff hJ hβ hg).1

lemma hadamard_B {ρ : ℝ} (hJ : ContDiffOn ℝ ∞ Jbar (univ ×ˢ ball (0 : ℂ) ρ))
    (hβ : β.rOut ≤ ρ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (KB Jbar β g) ∧ ∀ p, Bfun Jbar β g p = Bfun Jbar β g (p.1, 0) + KB Jbar β g p p.2 :=
  hadamard_integral_fderiv _ (Afun_Bfun_contDiff hJ hβ hg).2

/-- At the graph, the retracted structure is the original one. -/
lemma Jt_graph {r₁ : ℝ} (hβ : r₁ ≤ β.rIn) (hgr : ∀ x, ‖g x‖ ≤ r₁) (x : ℂ) :
    Jt Jbar β (x, g x + 0) = Jbar (x, g x) := by
  simp [Jt, rtr_eq β ((hgr x).trans hβ)]

lemma Afun_zero {r₁ : ℝ} (hβ : r₁ ≤ β.rIn) (hgr : ∀ x, ‖g x‖ ≤ r₁)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1) (x : ℂ) :
    Afun Jbar β g (x, 0) = 0 := by
  simp only [Afun]
  rw [Jt_graph hβ hgr x]
  exact Ablk_eq_zero _ _ (hgJ x)

lemma C0_sq {ρ r₁ : ℝ} (hβ : r₁ ≤ β.rIn) (hgr : ∀ x, ‖g x‖ ≤ r₁) (hr₁ : r₁ < ρ)
    (hsq : ∀ p ∈ univ ×ˢ ball (0 : ℂ) ρ, (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1) (x u : ℂ) :
    C0 Jbar β g x (C0 Jbar β g x u) = -u := by
  have hA := Afun_zero hβ hgr hgJ x
  simp only [Afun] at hA
  simp only [C0, Bfun]
  rw [Jt_graph hβ hgr x] at hA ⊢
  exact Bblk_sq _ _ (hsq _ ⟨mem_univ _, mem_ball_zero_iff.2 ((hgr x).trans_lt hr₁)⟩) hA u

end

end FiniteEnergyPlane.B3E

/-! B3E layer P2: the frame `Pf`, the plane identity and the local `∂̄` bound. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap
open scoped ContDiff Real

noncomputable section

variable (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (β : ContDiffBump (0 : ℂ)) (g ψ v : ℂ → ℂ)





/-- Standing hypotheses. -/
structure Hyp (ρ r₁ : ℝ) : Prop where
  hJ : ContDiffOn ℝ ∞ Jbar (univ ×ˢ ball (0 : ℂ) ρ)
  hsq : ∀ p ∈ univ ×ˢ ball (0 : ℂ) ρ, (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ)
  hrIn : r₁ ≤ β.rIn
  hrOut : β.rOut ≤ ρ
  hr₁ : r₁ < ρ
  hg : ContDiff ℝ ∞ g
  hψ : ContDiff ℝ ∞ ψ
  hv : ContDiff ℝ ∞ v
  hgr : ∀ x, ‖g x‖ ≤ r₁
  hvr : ∀ z, ‖v z‖ ≤ r₁
  hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1
  hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z)

variable {Jbar β g ψ v} {ρ r₁ : ℝ}

lemma Hyp.C0_contDiff (H : Hyp Jbar β g ψ v ρ r₁) : ContDiff ℝ ∞ (C0 Jbar β g) :=
  (Afun_Bfun_contDiff H.hJ H.hrOut H.hg).2.comp (contDiff_id.prodMk contDiff_const)

lemma Hyp.cc_contDiff (H : Hyp Jbar β g ψ v ρ r₁) : ContDiff ℝ ∞ (cc Jbar β g ψ) :=
  (H.C0_contDiff.comp H.hψ).clm_apply contDiff_const

lemma Hyp.C0_sq (H : Hyp Jbar β g ψ v ρ r₁) (x u : ℂ) : C0 Jbar β g x (C0 Jbar β g x u) = -u :=
  B3E.C0_sq H.hrIn H.hgr H.hr₁ H.hsq H.hgJ x u

lemma Hyp.cc_im (H : Hyp Jbar β g ψ v ρ r₁) (z : ℂ) : (cc Jbar β g ψ z).im ≠ 0 :=
  im_ne_zero_of_sq _ (H.C0_sq (ψ z))

lemma qL_eq (c : ℂ) : qL c = Complex.reCLM.smulRight (1 : ℂ) +
    Complex.imCLM.smulRight ((Complex.I - c.re) * ((c.im⁻¹ : ℝ) : ℂ)) := by
  simp [qL, div_eq_mul_inv]

lemma Hyp.Pf_contDiff (H : Hyp Jbar β g ψ v ρ r₁) : ContDiff ℝ ∞ (Pf Jbar β g ψ) := by
  have hc := H.cc_contDiff
  have hinv : ContDiff ℝ ∞ (fun z => ((cc Jbar β g ψ z).im)⁻¹) :=
    (Complex.imCLM.contDiff.comp hc).inv (fun z => H.cc_im z)
  have hW : ContDiff ℝ ∞ (fun z => (Complex.I - ((cc Jbar β g ψ z).re : ℂ)) *
      (((cc Jbar β g ψ z).im⁻¹ : ℝ) : ℂ)) :=
    (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hc))).mul
      (Complex.ofRealCLM.contDiff.comp hinv)
  have : Pf Jbar β g ψ = fun z => Complex.reCLM.smulRight (1 : ℂ) +
      Complex.imCLM.smulRight ((Complex.I - ((cc Jbar β g ψ z).re : ℂ)) *
        (((cc Jbar β g ψ z).im⁻¹ : ℝ) : ℂ)) := by
    funext z; exact qL_eq _
  rw [this]
  exact contDiff_const.add (contDiff_const.smulRight hW)

lemma Hyp.hd_contDiff (H : Hyp Jbar β g ψ v ρ r₁) : ContDiff ℝ ∞ (hd g ψ v) :=
  H.hv.sub (H.hg.comp H.hψ)

lemma Hyp.fderiv_hd (H : Hyp Jbar β g ψ v ρ r₁) (z : ℂ) :
    fderiv ℝ (hd g ψ v) z = fderiv ℝ v z - (fderiv ℝ g (ψ z)).comp (fderiv ℝ ψ z) := by
  have dv := (H.hv.differentiable (by simp)) z
  have dψ := (H.hψ.differentiable (by simp)) z
  have dg := (H.hg.differentiable (by simp)) (ψ z)
  exact (dv.hasFDerivAt.sub (dg.hasFDerivAt.comp z dψ.hasFDerivAt)).fderiv

/-- The plane identity. -/
theorem Hyp.plane_identity (H : Hyp Jbar β g ψ v ρ r₁) (z e : ℂ) :
    fderiv ℝ (fun y => Pf Jbar β g ψ y (v y - g (ψ y))) z (Complex.I * e) -
        Complex.I * fderiv ℝ (fun y => Pf Jbar β g ψ y (v y - g (ψ y))) z e =
      Lmap Jbar β g ψ v z e (v z - g (ψ z)) := by
  have dP := (H.Pf_contDiff.differentiable (by simp)) z
  have dh := (H.hd_contDiff.differentiable (by simp)) z
  have dψ := (H.hψ.differentiable (by simp)) z
  have dv := (H.hv.differentiable (by simp)) z
  have hζ : fderiv ℝ (fun y => Pf Jbar β g ψ y (v y - g (ψ y))) z =
      (Pf Jbar β g ψ z).comp (fderiv ℝ (hd g ψ v) z) +
        (fderiv ℝ (Pf Jbar β g ψ) z).flip (hd g ψ v z) :=
    fderiv_clm_apply dP dh
  -- the holomorphy relation
  have hprod : fderiv ℝ (fun y : ℂ => (ψ y, v y)) z = (fderiv ℝ ψ z).prod (fderiv ℝ v z) :=
    DifferentiableAt.fderiv_prodMk dψ dv
  have hrel : ∀ e : ℂ, (fderiv ℝ ψ z (Complex.I * e), fderiv ℝ v z (Complex.I * e)) =
      Jbar (ψ z, v z) (fderiv ℝ ψ z e, fderiv ℝ v z e) := by
    intro e
    have := congrArg (fun L : ℂ →L[ℝ] ℂ × ℂ => L e) (H.hhol z)
    simpa [hprod] using this
  have hJz : Jbar (ψ z, v z) = Jt Jbar β (ψ z, g (ψ z) + hd g ψ v z) := by
    simp [Jt, hd, rtr_eq β ((H.hvr z).trans H.hrIn)]
  rw [hJz] at hrel
  have key := dh_I _ (fderiv ℝ g (ψ z)) _ _ hrel e
  rw [← H.fderiv_hd] at key
  have hA : Ablk (Jt Jbar β (ψ z, g (ψ z) + hd g ψ v z)) (fderiv ℝ g (ψ z)) =
      KA Jbar β g (ψ z, hd g ψ v z) (hd g ψ v z) := by
    have h1 := (hadamard_A H.hJ H.hrOut H.hg).2 (ψ z, hd g ψ v z)
    rw [Afun_zero H.hrIn H.hgr H.hgJ, zero_add] at h1
    exact h1
  have hB : Bblk (Jt Jbar β (ψ z, g (ψ z) + hd g ψ v z)) (fderiv ℝ g (ψ z)) =
      C0 Jbar β g (ψ z) + KB Jbar β g (ψ z, hd g ψ v z) (hd g ψ v z) :=
    (hadamard_B H.hJ H.hrOut H.hg).2 (ψ z, hd g ψ v z)
  rw [hA, hB] at key
  have hint : ∀ u, Pf Jbar β g ψ z (C0 Jbar β g (ψ z) u) = Complex.I * Pf Jbar β g ψ z u :=
    fun u => qL_intertwine _ (H.C0_sq (ψ z)) u
  have hdef : (fun y => v y - g (ψ y)) = hd g ψ v := rfl
  rw [hζ]
  simp only [Lmap, add_apply, sub_apply, comp_apply, flip_apply, smul_apply, key, map_add,
    add_apply, hint, hdef, apply_apply]
  simp only [smul_eq_mul, hd]
  ring

lemma Hyp.Lmap_continuous (H : Hyp Jbar β g ψ v ρ r₁) (e : ℂ) :
    Continuous (fun z => Lmap Jbar β g ψ v z e) := by
  have hP := H.Pf_contDiff
  have hDP : Continuous (fderiv ℝ (Pf Jbar β g ψ)) := hP.continuous_fderiv (by simp)
  have hKA := (hadamard_A H.hJ H.hrOut H.hg).1.continuous
  have hKB := (hadamard_B H.hJ H.hrOut H.hg).1.continuous
  have hh := H.hd_contDiff
  have hin : Continuous (fun z => (ψ z, hd g ψ v z)) := H.hψ.continuous.prodMk hh.continuous
  have hDψ : Continuous (fderiv ℝ ψ) := H.hψ.continuous_fderiv (by simp)
  have hDh : Continuous (fderiv ℝ (hd g ψ v)) := hh.continuous_fderiv (by simp)
  have hap : Continuous (fun u : ℂ => ContinuousLinearMap.apply ℝ ℂ u :
      ℂ → (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ) := (ContinuousLinearMap.apply ℝ ℂ : ℂ →L[ℝ] _).continuous
  have h1 : Continuous (fun z => fderiv ℝ (Pf Jbar β g ψ) z (Complex.I * e)) :=
    hDP.clm_apply continuous_const
  have h2 : Continuous (fun z => Complex.I • fderiv ℝ (Pf Jbar β g ψ) z e) :=
    (hDP.clm_apply continuous_const).const_smul Complex.I
  have h3 : Continuous (fun z => (Pf Jbar β g ψ z).comp
      ((ContinuousLinearMap.apply ℝ ℂ (fderiv ℝ ψ z e)).comp (KA Jbar β g (ψ z, hd g ψ v z)))) :=
    hP.continuous.clm_comp ((hap.comp (hDψ.clm_apply continuous_const)).clm_comp (hKA.comp hin))
  have h4 : Continuous (fun z => (Pf Jbar β g ψ z).comp
      ((ContinuousLinearMap.apply ℝ ℂ (fderiv ℝ (hd g ψ v) z e)).comp
        (KB Jbar β g (ψ z, hd g ψ v z)))) :=
    hP.continuous.clm_comp ((hap.comp (hDh.clm_apply continuous_const)).clm_comp (hKB.comp hin))
  exact ((h1.sub h2).add h3).add h4

lemma qinvL_continuous : Continuous qinvL := by
  unfold qinvL
  exact continuous_const.add ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).continuous)

/-- The local `∂̄` bound. -/
theorem Hyp.local_bound (H : Hyp Jbar β g ψ v ρ r₁) (z₀ : ℂ) :
    ∃ r > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ r,
      ‖fderiv ℝ (fun y => Pf Jbar β g ψ y (v y - g (ψ y))) z 1 +
          Complex.I * fderiv ℝ (fun y => Pf Jbar β g ψ y (v y - g (ψ y))) z Complex.I‖ ≤
        M * ‖Pf Jbar β g ψ z (v z - g (ψ z))‖ := by
  have hcont : Continuous (fun z => ‖Lmap Jbar β g ψ v z 1‖ * ‖qinvL (cc Jbar β g ψ z)‖) :=
    (H.Lmap_continuous 1).norm.mul (qinvL_continuous.comp H.cc_contDiff.continuous).norm
  obtain ⟨z₁, -, hz₁⟩ := (isCompact_closedBall z₀ 1).exists_isMaxOn
    (nonempty_closedBall.2 zero_le_one) hcont.continuousOn
  refine ⟨1, one_pos, ‖Lmap Jbar β g ψ v z₁ 1‖ * ‖qinvL (cc Jbar β g ψ z₁)‖, fun z hz => ?_⟩
  have hid := H.plane_identity z 1
  rw [mul_one] at hid
  set D := fderiv ℝ (fun y => Pf Jbar β g ψ y (v y - g (ψ y))) z
  have : D 1 + Complex.I * D Complex.I =
      Complex.I * Lmap Jbar β g ψ v z 1 (v z - g (ψ z)) := by
    rw [← hid]; ring_nf; rw [Complex.I_sq]; ring
  rw [this, norm_mul, Complex.norm_I, one_mul]
  have hh : v z - g (ψ z) = qinvL (cc Jbar β g ψ z) (Pf Jbar β g ψ z (v z - g (ψ z))) :=
    (qinvL_qL _ (H.cc_im z) _).symm
  calc ‖Lmap Jbar β g ψ v z 1 (v z - g (ψ z))‖
      ≤ ‖Lmap Jbar β g ψ v z 1‖ * ‖v z - g (ψ z)‖ := le_opNorm _ _
    _ ≤ ‖Lmap Jbar β g ψ v z 1‖ * (‖qinvL (cc Jbar β g ψ z)‖ *
          ‖Pf Jbar β g ψ z (v z - g (ψ z))‖) := by
        gcongr
        conv_lhs => rw [hh]
        exact le_opNorm _ _
    _ = (‖Lmap Jbar β g ψ v z 1‖ * ‖qinvL (cc Jbar β g ψ z)‖) *
          ‖Pf Jbar β g ψ z (v z - g (ψ z))‖ := by ring
    _ ≤ _ := by
        have hm := hz₁ (mem_closedBall.2 (le_of_lt (mem_ball.1 hz)))
        simp only [Set.mem_setOf_eq] at hm
        exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)

end

end FiniteEnergyPlane.B3E

/-! B3E layer M: matrices of real-linear maps of `ℂ`, `vecToC`/`cToVec`, the derivative of
`cylInf` (copied, renamed, from `Scratch/JWQ_S1`, `JWQ_N6`, `SMF_A`, `FAS_D`). -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section



/-- `reIm i` as a continuous real-linear map. -/
def reImCLM : Fin 1 ⊕ Fin 1 → ℂ →L[ℝ] ℝ :=
  Sum.elim (fun _ => Complex.reCLM) (fun _ => Complex.imCLM)

theorem reImCLM_apply (i : Fin 1 ⊕ Fin 1) (y : ℂ) : reImCLM i y = reIm i y := by
  rcases i with i | i <;> rfl


theorem vecToC_eq (a : Vec 1) :
    vecToC a = (a (Sum.inl 0)) • (1 : ℂ) + (a (Sum.inr 0)) • Complex.I := by
  apply Complex.ext <;> simp [vecToC]

theorem vecToC_cMat (T : ℂ →L[ℝ] ℂ) (a : Vec 1) :
    vecToC (Matrix.toEuclideanLin (cMat T) a) = T (vecToC a) := by
  rw [vecToC_eq a, map_add, map_smul, map_smul]
  apply Complex.ext <;>
  simp [vecToC, cMat, reIm, basisC, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type] <;> ring

theorem vecToC_injective : Function.Injective vecToC := by
  intro a b h
  ext i
  rcases i with i | i <;> obtain rfl : i = 0 := Subsingleton.elim _ _
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

theorem cMat_apply (T : ℂ →L[ℝ] ℂ) (i j : Fin 1 ⊕ Fin 1) :
    cMat T i j = reIm i (T (basisC j)) := rfl

/-- An entry of `cMat` as a continuous linear functional. -/
def entC (i j : Fin 1 ⊕ Fin 1) : (ℂ →L[ℝ] ℂ) →L[ℝ] ℝ :=
  (reImCLM i).comp (ContinuousLinearMap.apply ℝ ℂ (basisC j))

lemma entC_apply (i j : Fin 1 ⊕ Fin 1) (T : ℂ →L[ℝ] ℂ) : entC i j T = cMat T i j := by
  simp [entC, cMat_apply, reImCLM_apply]

lemma vecToC_J₀ (a : Vec 1) :
    vecToC (Matrix.toEuclideanLin (J₀ 1) a) = Complex.I * vecToC a := by
  apply Complex.ext <;>
    simp [vecToC, J₀, Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec, dotProduct,
      Matrix.fromBlocks, Fintype.sum_sum_type]

lemma cToVec_vecToC (a : Vec 1) : cToVec (vecToC a) = a := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [cToVec, vecToC]

lemma vecToC_cToVec (z : ℂ) : vecToC (cToVec z) = z := by
  apply Complex.ext <;> simp [cToVec, vecToC]

/-- `cToVec` as a continuous real-linear map. -/
def cToVecL : ℂ →L[ℝ] Vec 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := cToVec
      map_add' := fun a b => by ext i; rcases i with i | i <;> simp [cToVec]
      map_smul' := fun c a => by ext i; rcases i with i | i <;> simp [cToVec] }

@[simp] lemma cToVecL_apply (z : ℂ) : cToVecL z = cToVec z := rfl

/-- `vecToC` as a continuous real-linear map. -/
def vecToCL : Vec 1 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := vecToC
      map_add' := fun a b => by apply Complex.ext <;> simp [vecToC]
      map_smul' := fun c a => by apply Complex.ext <;> simp [vecToC] }

@[simp] lemma vecToCL_apply (a : Vec 1) : vecToCL a = vecToC a := rfl

lemma norm_cToVec (z : ℂ) : ‖cToVec z‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq, Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp [cToVec, Fintype.sum_sum_type, Real.norm_eq_abs, sq_abs, sq]

lemma cyl_eq (s t : ℝ) :
    cylInf s t = Complex.exp ((2 * π : ℝ) • ((s : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold cylInf ccwLoop
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The derivative of the cylindrical coordinates. -/
lemma cyl_hasFDerivAt (q : ℝ × ℝ) :
    ∃ L : ℝ × ℝ →L[ℝ] ℂ, HasFDerivAt (fun q : ℝ × ℝ => cylInf q.1 q.2) L q ∧
      L (1, 0) = ((2 * π : ℝ) : ℂ) * cylInf q.1 q.2 ∧
      L (0, 1) = Complex.I * (((2 * π : ℝ) : ℂ) * cylInf q.1 q.2) := by
  set Λ : ℝ × ℝ →L[ℝ] ℂ := (2 * π : ℝ) • ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (1 : ℂ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I) with hΛ
  have hval : ∀ q : ℝ × ℝ, Λ q = (2 * π : ℝ) • ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) := by
    intro q
    simp [hΛ]
  have hfun : (fun q : ℝ × ℝ => cylInf q.1 q.2) = fun q => Complex.exp (Λ q) := by
    funext q
    rw [hval, cyl_eq]
  have h := Λ.hasFDerivAt (x := q)
  refine ⟨Complex.exp (Λ q) • Λ, ?_, ?_, ?_⟩
  · rw [hfun]; exact h.cexp
  · rw [ContinuousLinearMap.smul_apply, hval, cyl_eq, hval]
    simp [mul_comm]
  · rw [ContinuousLinearMap.smul_apply, hval, cyl_eq, hval]
    simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_add, one_mul, Complex.real_smul,
      smul_eq_mul]
    ring

lemma cyl_contDiff : ContDiff ℝ ∞ (fun q : ℝ × ℝ => cylInf q.1 q.2) := by
  have : (fun q : ℝ × ℝ => cylInf q.1 q.2) = fun q => Complex.exp ((2 * π : ℝ) •
      (Complex.ofRealCLM q.1 + Complex.ofRealCLM q.2 * Complex.I)) := by
    funext q; rw [cyl_eq]; rfl
  rw [this]
  refine Complex.contDiff_exp.comp (ContDiff.const_smul ((2 * π : ℝ)) ?_)
  exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).add
    ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)

lemma cyl_per (s t : ℝ) : cylInf s (t + 1) = cylInf s t := by
  rw [cyl_eq, cyl_eq]
  have : (2 * π : ℝ) • ((s : ℂ) + ((t + 1 : ℝ) : ℂ) * Complex.I) =
      (2 * π : ℝ) • ((s : ℂ) + (t : ℂ) * Complex.I) + 2 * π * Complex.I := by
    simp only [Complex.real_smul]; push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

end

end FiniteEnergyPlane.B3E

/-! B3E layer C: the solution `wf` and the coefficient `Sf` on the cylinder at `∞`. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

variable (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (β : ContDiffBump (0 : ℂ)) (g ψ v : ℂ → ℂ)






variable {Jbar β g ψ v} {ρ r₁ : ℝ}

lemma Hyp.ζf_contDiff (H : Hyp Jbar β g ψ v ρ r₁) : ContDiff ℝ ∞ (ζf Jbar β g ψ v) :=
  H.Pf_contDiff.clm_apply H.hd_contDiff

lemma Hyp.wf_contDiff (H : Hyp Jbar β g ψ v ρ r₁) : ContDiff ℝ ∞ (wf Jbar β g ψ v) :=
  cToVecL.contDiff.comp (H.ζf_contDiff.comp cyl_contDiff)

lemma Hyp.Lmap_contDiff (H : Hyp Jbar β g ψ v ρ r₁) {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {zf ef : X → ℂ} (hz : ContDiff ℝ ∞ zf) (he : ContDiff ℝ ∞ ef) :
    ContDiff ℝ ∞ (fun x => Lmap Jbar β g ψ v (zf x) (ef x)) := by
  have hP := H.Pf_contDiff
  have hDP : ContDiff ℝ ∞ (fderiv ℝ (Pf Jbar β g ψ)) := hP.fderiv_right (m := ∞) le_rfl
  have hKA := (hadamard_A H.hJ H.hrOut H.hg).1
  have hKB := (hadamard_B H.hJ H.hrOut H.hg).1
  have hh := H.hd_contDiff
  have hin : ContDiff ℝ ∞ (fun x => (ψ (zf x), hd g ψ v (zf x))) :=
    (H.hψ.comp hz).prodMk (hh.comp hz)
  have hDψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := H.hψ.fderiv_right (m := ∞) le_rfl
  have hDh : ContDiff ℝ ∞ (fderiv ℝ (hd g ψ v)) := hh.fderiv_right (m := ∞) le_rfl
  have hap : ContDiff ℝ ∞ (fun u : ℂ => ContinuousLinearMap.apply ℝ ℂ u :
      ℂ → (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ) := (ContinuousLinearMap.apply ℝ ℂ : ℂ →L[ℝ] _).contDiff
  have h1 : ContDiff ℝ ∞ (fun x => fderiv ℝ (Pf Jbar β g ψ) (zf x) (Complex.I * ef x)) :=
    (hDP.comp hz).clm_apply (contDiff_const.mul he)
  have h2 : ContDiff ℝ ∞ (fun x => Complex.I • fderiv ℝ (Pf Jbar β g ψ) (zf x) (ef x)) :=
    ((hDP.comp hz).clm_apply he).const_smul Complex.I
  have h3 : ContDiff ℝ ∞ (fun x => (Pf Jbar β g ψ (zf x)).comp
      ((ContinuousLinearMap.apply ℝ ℂ (fderiv ℝ ψ (zf x) (ef x))).comp
        (KA Jbar β g (ψ (zf x), hd g ψ v (zf x))))) :=
    (hP.comp hz).clm_comp ((hap.comp ((hDψ.comp hz).clm_apply he)).clm_comp (hKA.comp hin))
  have h4 : ContDiff ℝ ∞ (fun x => (Pf Jbar β g ψ (zf x)).comp
      ((ContinuousLinearMap.apply ℝ ℂ (fderiv ℝ (hd g ψ v) (zf x) (ef x))).comp
        (KB Jbar β g (ψ (zf x), hd g ψ v (zf x))))) :=
    (hP.comp hz).clm_comp ((hap.comp ((hDh.comp hz).clm_apply he)).clm_comp (hKB.comp hin))
  exact ((h1.sub h2).add h3).add h4

lemma qinvL_contDiff : ContDiff ℝ ∞ qinvL := by
  unfold qinvL
  exact contDiff_const.add ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).contDiff)

lemma Hyp.Tf_contDiff (H : Hyp Jbar β g ψ v ρ r₁) : ContDiff ℝ ∞ (Tf Jbar β g ψ v) := by
  have hc2 : ContDiff ℝ ∞ (c2 : ℝ × ℝ → ℂ) := contDiff_const.mul cyl_contDiff
  exact ((H.Lmap_contDiff cyl_contDiff hc2).clm_comp
    (qinvL_contDiff.comp (H.cc_contDiff.comp cyl_contDiff))).const_smul (-Complex.I)

lemma Hyp.Sf_contDiff (H : Hyp Jbar β g ψ v ρ r₁) (i j : Fin 1 ⊕ Fin 1) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => Sf Jbar β g ψ v p i j) := by
  have : (fun p : ℝ × ℝ => Sf Jbar β g ψ v p i j) = fun p => entC i j (Tf Jbar β g ψ v p) := by
    funext p; rw [entC_apply]; rfl
  rw [this]
  exact (entC i j).contDiff.comp H.Tf_contDiff

lemma Sf_per (s t : ℝ) : Sf Jbar β g ψ v (s, t + 1) = Sf Jbar β g ψ v (s, t) := by
  simp only [Sf, Tf, c2, cyl_per]

lemma wf_per (s t : ℝ) : wf Jbar β g ψ v (s, t + 1) = wf Jbar β g ψ v (s, t) := by
  simp only [wf, cyl_per]

lemma vecToC_wf (s t : ℝ) : vecToC (wf Jbar β g ψ v (s, t)) =
    Pf Jbar β g ψ (cylInf s t) (v (cylInf s t) - g (ψ (cylInf s t))) := by
  simp [wf, ζf, vecToC_cToVec]

/-- The partial derivatives of `wf`. -/
lemma Hyp.partials_wf (H : Hyp Jbar β g ψ v ρ r₁) (p : ℝ × ℝ) :
    partialS (wf Jbar β g ψ v) p =
        cToVec (fderiv ℝ (ζf Jbar β g ψ v) (cylInf p.1 p.2) (c2 p)) ∧
      partialT (wf Jbar β g ψ v) p =
        cToVec (fderiv ℝ (ζf Jbar β g ψ v) (cylInf p.1 p.2) (Complex.I * c2 p)) := by
  obtain ⟨L, hL, hL1, hL2⟩ := cyl_hasFDerivAt p
  have hζ := ((H.ζf_contDiff.differentiable (by simp)) (cylInf p.1 p.2)).hasFDerivAt
  have h2 := hζ.comp p hL
  have hw : HasFDerivAt (wf Jbar β g ψ v)
      (cToVecL.comp ((fderiv ℝ (ζf Jbar β g ψ v) (cylInf p.1 p.2)).comp L)) p :=
    cToVecL.hasFDerivAt.comp p h2
  refine ⟨?_, ?_⟩
  · simp only [partialS, hw.fderiv, comp_apply, hL1, cToVecL_apply, c2]
  · simp only [partialT, hw.fderiv, comp_apply, hL2, cToVecL_apply, c2]

/-- The end equation `∂ₛw + J₀ ∂ₜw + S w = 0`. -/
theorem Hyp.crOp_eq_zero (H : Hyp Jbar β g ψ v ρ r₁) (p : ℝ × ℝ) :
    crOp (Sf Jbar β g ψ v) (wf Jbar β g ψ v) p = 0 := by
  apply vecToC_injective
  obtain ⟨hs, ht⟩ := H.partials_wf p
  set z := cylInf p.1 p.2
  have hid := H.plane_identity z (c2 p)
  have hζdef : (fun y => Pf Jbar β g ψ y (v y - g (ψ y))) = ζf Jbar β g ψ v := rfl
  rw [hζdef] at hid
  have hwz : vecToC (wf Jbar β g ψ v p) = ζf Jbar β g ψ v z := by simp [wf, vecToC_cToVec, z]
  have hT : Tf Jbar β g ψ v p (vecToC (wf Jbar β g ψ v p)) =
      -Complex.I * Lmap Jbar β g ψ v z (c2 p) (v z - g (ψ z)) := by
    rw [hwz]
    simp only [Tf, smul_apply, comp_apply, smul_eq_mul]
    rw [show ζf Jbar β g ψ v z = Pf Jbar β g ψ z (v z - g (ψ z)) from rfl, Pf,
      qinvL_qL _ (H.cc_im z)]
  have hv0 : vecToC (0 : Vec 1) = 0 := by apply Complex.ext <;> simp [vecToC]
  rw [hv0, crOp]
  have hadd : ∀ a b c : Vec 1, vecToC (a + b + c) = vecToC a + vecToC b + vecToC c := by
    intro a b c; simp only [← vecToCL_apply, map_add]
  rw [hadd, vecToC_J₀, Sf, vecToC_cMat, hT, hs, ht, vecToC_cToVec, vecToC_cToVec]
  have : fderiv ℝ (ζf Jbar β g ψ v) z (Complex.I * c2 p) =
      Complex.I * fderiv ℝ (ζf Jbar β g ψ v) z (c2 p) +
        Lmap Jbar β g ψ v z (c2 p) (v z - g (ψ z)) := by
    rw [← hid]; ring
  rw [this]
  ring_nf
  rw [Complex.I_sq]
  ring

end

end FiniteEnergyPlane.B3E

/-! B3E layer E: bounded-derivative calculus on the end `s → ∞` of `ℝ × ℝ`. -/

namespace FiniteEnergyPlane.B3E


open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Real Nat

noncomputable section

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- All derivatives bounded far out on the end. -/
def Bd (f : ℝ × ℝ → F) : Prop :=
  ∀ m : ℕ, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m f (s, t)‖ ≤ C

/-- Uniform version of `Bd` up to order `k`. -/
lemma Bd.upTo {f : ℝ × ℝ → F} (hf : Bd f) (k : ℕ) :
    ∃ B T : ℝ, 0 ≤ B ∧ ∀ i ≤ k, ∀ s ≥ T, ∀ t : ℝ, ‖iteratedFDeriv ℝ i f (s, t)‖ ≤ B := by
  choose Ci si hCi using hf
  refine ⟨∑ i ∈ Finset.range (k + 1), |Ci i|, ∑ i ∈ Finset.range (k + 1), |si i|,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, fun i hi s hs t => ?_⟩
  have hmem : i ∈ Finset.range (k + 1) := Finset.mem_range.2 (by omega)
  have hsi : si i ≤ s := (le_abs_self _).trans ((Finset.single_le_sum (f := fun i => |si i|)
    (fun _ _ => abs_nonneg _) hmem).trans hs)
  exact (hCi i s hsi t).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |Ci i|) (fun _ _ => abs_nonneg _) hmem))

lemma bd_of_le {f : ℝ × ℝ → F} (h : ∀ m : ℕ, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
    ‖iteratedFDeriv ℝ m f (s, t)‖ ≤ C) : Bd f := h

lemma bd_const (c : F) : Bd (fun _ : ℝ × ℝ => c) := by
  intro m
  refine ⟨‖c‖, 0, fun s _ t => ?_⟩
  rcases m with _ | m
  · simp
  · rw [iteratedFDeriv_const_of_ne (by omega)]; simp

lemma bd_add {f g : ℝ × ℝ → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hbf : Bd f)
    (hbg : Bd g) : Bd (fun p => f p + g p) := by
  intro m
  obtain ⟨C₁, s₁, h₁⟩ := hbf m
  obtain ⟨C₂, s₂, h₂⟩ := hbg m
  refine ⟨C₁ + C₂, max s₁ s₂, fun s hs t => ?_⟩
  rw [show (fun p => f p + g p) = f + g from rfl, iteratedFDeriv_add_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.contDiffAt.of_le (by exact_mod_cast le_top))]
  exact (norm_add_le _ _).trans (add_le_add (h₁ s (le_of_max_le_left hs) t)
    (h₂ s (le_of_max_le_right hs) t))

lemma bd_neg {f : ℝ × ℝ → F} (hbf : Bd f) : Bd (fun p => -f p) := by
  intro m
  obtain ⟨C₁, s₁, h₁⟩ := hbf m
  refine ⟨C₁, s₁, fun s hs t => ?_⟩
  rw [show (fun p => -f p) = -f from rfl, iteratedFDeriv_neg_apply, norm_neg]; exact h₁ s hs t

lemma bd_sub {f g : ℝ × ℝ → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hbf : Bd f)
    (hbg : Bd g) : Bd (fun p => f p - g p) := by
  simpa [sub_eq_add_neg] using bd_add hf hg.neg hbf (bd_neg hbg)

/-- Bilinear images of bounded families. -/
lemma bd_bilin (B : F →L[ℝ] G →L[ℝ] H) {f : ℝ × ℝ → F} {g : ℝ × ℝ → G}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hbf : Bd f) (hbg : Bd g) :
    Bd (fun p => B (f p) (g p)) := by
  intro m
  obtain ⟨B₁, T₁, hB₁, h₁⟩ := hbf.upTo m
  obtain ⟨B₂, T₂, hB₂, h₂⟩ := hbg.upTo m
  refine ⟨‖B‖ * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B₁ * B₂, max T₁ T₂,
    fun s hs t => ?_⟩
  refine (B.norm_iteratedFDeriv_le_of_bilinear hf hg (s, t) (by exact_mod_cast le_top)).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by positivity)
  have e1 := h₁ i (by simpa [Nat.lt_succ_iff] using hi) s (le_of_max_le_left hs) t
  have e2 := h₂ (m - i) (Nat.sub_le _ _) s (le_of_max_le_right hs) t
  exact mul_le_mul (mul_le_mul_of_nonneg_left e1 (Nat.cast_nonneg _)) e2 (by positivity)
    (mul_nonneg (Nat.cast_nonneg _) hB₁)

lemma bd_clm (L : F →L[ℝ] G) {f : ℝ × ℝ → F} (hf : ContDiff ℝ ∞ f) (hbf : Bd f) :
    Bd (fun p => L (f p)) := by
  intro m
  obtain ⟨C, s₁, h⟩ := hbf m
  refine ⟨‖L‖ * C, s₁, fun s hs t => ?_⟩
  rw [show (fun p => L (f p)) = L ∘ f from rfl, L.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast le_top)]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_left (h s hs t) (norm_nonneg _))

lemma bd_of_expDecay {f : ℝ × ℝ → F} {b : ℝ} (hb : 0 ≤ b) (hf : ExpDecayCInfty f b) : Bd f := by
  intro m
  obtain ⟨B, T, -, h⟩ := BT.bound_of_expDecay hb hf m
  exact ⟨B, T, fun s hs t => h m le_rfl s hs t⟩

/-- Interpolation: bounded derivatives and `C⁰` exponential decay give `C^∞` decay at any
smaller rate. -/
lemma expDecay_of_bd {f : ℝ × ℝ → F} (hf : ContDiff ℝ ∞ f) (hbf : Bd f) {b C s₀ : ℝ}
    (h0 : ∀ s ≥ s₀, ∀ t : ℝ, ‖f (s, t)‖ ≤ C * Real.exp (-(b * s))) (hb : 0 < b) :
    ∀ b' < b, ExpDecayCInfty f b' := by
  have hT : TendstoZeroUnif f := by
    intro ε hε
    have ht : Tendsto (fun s : ℝ => C * Real.exp (-(b * s))) atTop (𝓝 0) := by
      have : Tendsto (fun s : ℝ => Real.exp (-(b * s))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
          (tendsto_id.const_mul_atTop hb))
      simpa using this.const_mul C
    obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 ((ht.eventually (ge_mem_nhds hε)).and
      (eventually_ge_atTop s₀))
    exact ⟨s₂, fun s hs t => (h0 s (hs₂ s hs).2 t).trans (hs₂ s hs).1⟩
  have hZ := tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd f 0 hf.contDiffOn hT hbf
  exact expDecayCInfty_of_tendstoZeroCInfty f hZ b C s₀ h0

/-- Faà di Bruno for a family of inner maps with uniform bounds. -/
lemma bd_comp_family {ι : Type*} (Φ : E → F) (V : Set E) (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ ∞ Φ V) (X : ι → ℝ × ℝ → E) (hX : ∀ θ, ContDiff ℝ ∞ (X θ))
    (s₀ : ℝ) (hXV : ∀ θ, ∀ s > s₀, ∀ t, X θ (s, t) ∈ V)
    (hΦb : ∀ n : ℕ, ∃ C : ℝ, ∀ θ, ∀ s > s₀, ∀ t, ∀ i ≤ n,
      ‖iteratedFDeriv ℝ i Φ (X θ (s, t))‖ ≤ C)
    (hXb : ∀ n : ℕ, ∃ D : ℝ, ∀ θ, ∀ s > s₀, ∀ t, ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (X θ) (s, t)‖ ≤ D) :
    ∀ n : ℕ, ∃ K : ℝ, ∀ θ, ∀ s > s₀, ∀ t,
      ‖iteratedFDeriv ℝ n (fun p => Φ (X θ p)) (s, t)‖ ≤ K := by
  intro n
  obtain ⟨C, hC⟩ := hΦb n
  obtain ⟨D, hD⟩ := hXb n
  refine ⟨n ! * C * (max 1 D) ^ n, fun θ s hs t => ?_⟩
  have hU : IsOpen (Ioi s₀ ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  refine BT.fdb (q := (s, t)) hU hV hΦ (hX θ).contDiffOn (fun q hq => ?_) ⟨hs, mem_univ t⟩
    (fun i hi => hC θ s hs t i hi) (fun i hi1 hi => ?_)
  · obtain ⟨hq1, -⟩ := hq
    simpa using hXV θ q.1 hq1 q.2
  · refine (hD θ s hs t i hi1 hi).trans ((le_max_right 1 D).trans ?_)
    exact le_self_pow₀ (le_max_left 1 D) (by omega)

/-- Parameter integrals over `[0, 1]` of uniformly bounded families. -/
lemma bd_integral (Fθ : ℝ × ℝ → ℝ → F) [CompleteSpace F]
    (hF : ContDiff ℝ ∞ (Function.uncurry Fθ))
    (hb : ∀ m : ℕ, ∃ C s₁ : ℝ, ∀ θ ∈ Icc (0 : ℝ) 1, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p => Fθ p θ) (s, t)‖ ≤ C) :
    Bd (fun p => ∫ θ in (0 : ℝ)..1, Fθ p θ) := by
  intro m
  obtain ⟨C, s₁, h⟩ := hb m
  exact ⟨C, s₁, fun s hs t =>
    norm_iteratedFDeriv_intervalIntegral_le hF m (s, t) C (fun θ hθ => h θ hθ s hs t)⟩

end

end FiniteEnergyPlane.B3E

/-! B3E layer J: the structure in cylindrical coordinates, facts about `Jinf`, and a periodic
Lipschitz bound. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

/-- `2π e^{2π(s+it)}`. -/
def lam (s t : ℝ) : ℂ := ((2 * π : ℝ) : ℂ) * cylInf s t

lemma lam_ne (s t : ℝ) : lam s t ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) (BT.cylInf_ne_zero s t)

/-- Multiplication by `c` as a real-linear map. -/
def mulL (c : ℂ) : ℂ →L[ℝ] ℂ := c • ContinuousLinearMap.id ℝ ℂ

@[simp] lemma mulL_apply (c u : ℂ) : mulL c u = c * u := by simp [mulL]

lemma cylScale_apply (s t : ℝ) (v : ℂ × ℂ) : cylScale s t v = (lam s t * v.1, v.2) := rfl

lemma cylScaleInv_apply (s t : ℝ) (v : ℂ × ℂ) :
    cylScaleInv s t v = ((lam s t)⁻¹ * v.1, v.2) := rfl

lemma Jbar_cyl (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (s t : ℝ) (w : ℂ) (v : ℂ × ℂ) :
    Jbar (cylInf s t, w) v = cylScale s t (cylJ Jbar s t w (cylScaleInv s t v)) := by
  have h1 : cylScaleInv s t (cylScale s t v) = v := by
    rw [cylScaleInv_apply, cylScale_apply]
    simp [← mul_assoc, inv_mul_cancel₀ (lam_ne s t)]
  have h2 : ∀ u, cylScale s t (cylScaleInv s t u) = u := by
    intro u
    rw [cylScaleInv_apply, cylScale_apply]
    simp [← mul_assoc, mul_inv_cancel₀ (lam_ne s t)]
  simp only [cylJ, comp_apply, h2]

section blocks
variable (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (s t : ℝ) (w : ℂ)

lemma J11_cyl (u : ℂ) : J11 (Jbar (cylInf s t, w)) u =
    lam s t * J11 (cylJ Jbar s t w) ((lam s t)⁻¹ * u) := by
  have h := congrArg Prod.fst (Jbar_cyl Jbar s t w (u, 0))
  rw [cylScaleInv_apply, cylScale_apply] at h
  simp only [mul_zero] at h
  rw [show J11 (Jbar (cylInf s t, w)) u = (Jbar (cylInf s t, w) (u, 0)).1 from rfl, h]
  rfl

lemma J12_cyl (u : ℂ) : J12 (Jbar (cylInf s t, w)) u = lam s t * J12 (cylJ Jbar s t w) u := by
  have h := congrArg Prod.fst (Jbar_cyl Jbar s t w (0, u))
  rw [cylScaleInv_apply, cylScale_apply] at h
  simp only [mul_zero] at h
  rw [show J12 (Jbar (cylInf s t, w)) u = (Jbar (cylInf s t, w) (0, u)).1 from rfl, h]
  rfl

lemma J21_cyl (u : ℂ) : J21 (Jbar (cylInf s t, w)) u =
    J21 (cylJ Jbar s t w) ((lam s t)⁻¹ * u) := by
  have h := congrArg Prod.snd (Jbar_cyl Jbar s t w (u, 0))
  rw [cylScaleInv_apply, cylScale_apply] at h
  simp only at h
  rw [show J21 (Jbar (cylInf s t, w)) u = (Jbar (cylInf s t, w) (u, 0)).2 from rfl, h]
  rfl

lemma J22_cyl (u : ℂ) : J22 (Jbar (cylInf s t, w)) u = J22 (cylJ Jbar s t w) u := by
  have h := congrArg Prod.snd (Jbar_cyl Jbar s t w (0, u))
  rw [cylScaleInv_apply, cylScale_apply] at h
  simp only [mul_zero] at h
  rw [show J22 (Jbar (cylInf s t, w)) u = (Jbar (cylInf s t, w) (0, u)).2 from rfl, h]
  rfl

/-- The re-centred blocks in cylindrical coordinates. -/
lemma Ablk_cyl (G : ℂ →L[ℝ] ℂ) (u : ℂ) :
    Ablk (Jbar (cylInf s t, w)) G u =
      Ablk (cylJ Jbar s t w) (G.comp (mulL (lam s t))) ((lam s t)⁻¹ * u) := by
  have hl : lam s t * ((lam s t)⁻¹ * u) = u := by
    rw [← mul_assoc, mul_inv_cancel₀ (lam_ne s t), one_mul]
  simp only [Ablk, sub_apply, add_apply, comp_apply, J11_cyl, J12_cyl, J21_cyl, J22_cyl,
    mulL_apply, hl]

lemma Bblk_cyl (G : ℂ →L[ℝ] ℂ) (u : ℂ) :
    Bblk (Jbar (cylInf s t, w)) G u = Bblk (cylJ Jbar s t w) (G.comp (mulL (lam s t))) u := by
  simp only [Bblk, sub_apply, comp_apply, J12_cyl, J22_cyl, mulL_apply]

end blocks

/-! ### `Jinf` along `w = 0` -/

lemma jStd_apply (v : ℂ × ℂ) : jStd v = (Complex.I * v.1, Complex.I * v.2) := rfl

lemma cylJ_zero {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (s t : ℝ) : cylJ Jbar s t 0 = jStd := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [cylJ, comp_apply, h0]
  rw [cylScale_apply, jStd_apply, cylScaleInv_apply, jStd_apply]
  have hl := lam_ne s t
  ext
  · simp only
    field_simp
  · rfl

/-- The tube difference. -/
def fd (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (q : ℝ × ℝ × ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ := cylJ Jbar q.1 q.2.1 q.2.2 - Jinf (q.2.1, q.2.2)

variable {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}

lemma tendsto_cylJ (hb : 0 < b) (hdec : ExpDecayCInftyTube (fd Jbar Jinf) ρ b) (t : ℝ) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) ρ) :
    Tendsto (fun s => cylJ Jbar s t w) atTop (𝓝 (Jinf (t, w))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨C, s₁, hC⟩ := hdec.2 0
  have ht : Tendsto (fun s : ℝ => C * Real.exp (-(b * s))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hb)).const_mul C
    simpa [Function.comp_def] using this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_atTop.2 ⟨s₁, fun s hs => ?_⟩) ht
  have := hC s hs t w hw
  simpa [norm_iteratedFDeriv_zero, fd] using this

lemma cylJ_sq (hsq : ∀ p ∈ univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (s t : ℝ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ) (v : ℂ × ℂ) :
    cylJ Jbar s t w (cylJ Jbar s t w v) = -v := by
  have h1 : ∀ u, cylScaleInv s t (cylScale s t u) = u := by
    intro u
    rw [cylScaleInv_apply, cylScale_apply]
    simp [← mul_assoc, inv_mul_cancel₀ (lam_ne s t)]
  have h := congrArg (fun L : ℂ × ℂ →L[ℝ] ℂ × ℂ => L (cylScale s t v))
    (hsq (cylInf s t, w) ⟨mem_univ _, hw⟩)
  have h2 : ∀ u, cylScale s t (cylScaleInv s t u) = u := by
    intro u
    rw [cylScaleInv_apply, cylScale_apply]
    simp [← mul_assoc, mul_inv_cancel₀ (lam_ne s t)]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply] at h
  simp only [cylJ, ContinuousLinearMap.comp_apply]
  rw [h2, h, map_neg, h1]

lemma Jinf_zero (hb : 0 < b) (hρ : 0 < ρ) (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (hdec : ExpDecayCInftyTube (fd Jbar Jinf) ρ b) (t : ℝ) : Jinf (t, 0) = jStd := by
  have h := tendsto_cylJ hb hdec t (mem_ball_self hρ)
  simp only [cylJ_zero h0] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

lemma Jinf_sq (hb : 0 < b) (hsq : ∀ p ∈ univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (hdec : ExpDecayCInftyTube (fd Jbar Jinf) ρ b) (t : ℝ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ) :
    (Jinf (t, w)).comp (Jinf (t, w)) = -ContinuousLinearMap.id ℝ (ℂ × ℂ) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h := tendsto_cylJ hb hdec t hw
  have hc : Continuous fun L : ℂ × ℂ →L[ℝ] ℂ × ℂ => L (L v) :=
    continuous_id.clm_apply (continuous_id.clm_apply continuous_const)
  have h2 := (hc.tendsto _).comp h
  have e : ((fun L : ℂ × ℂ →L[ℝ] ℂ × ℂ => L (L v)) ∘ fun s => cylJ Jbar s t w) = fun _ => -v := by
    funext s; exact cylJ_sq hsq s t hw v
  rw [e] at h2
  simpa using tendsto_nhds_unique h2 tendsto_const_nhds

/-- The `w`-derivative of `Jinf` along `w = 0`. -/
def Kd (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (τ : ℝ) : ℂ →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ) :=
  fderiv ℝ (fun w : ℂ => Jinf (τ, w)) 0

/-- `a ↦ [(∂_w Jinf a)(1, 0)]₂`. -/
def Minf (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (τ : ℝ) : ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.snd ℝ ℂ ℂ).comp (ContinuousLinearMap.apply ℝ (ℂ × ℂ) ((1 : ℂ), (0 : ℂ)))).comp
    (Kd Jinf τ)

/-- `a ↦ [(∂_w Jinf a)(i, 0)]₂`. -/
def Tinf (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (τ : ℝ) : ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.snd ℝ ℂ ℂ).comp
    (ContinuousLinearMap.apply ℝ (ℂ × ℂ) (Complex.I, (0 : ℂ)))).comp (Kd Jinf τ)

lemma Tinf_eq (hρ : 0 < ρ) (hb : 0 < b) (hJi : ContDiffOn ℝ ∞ Jinf (univ ×ˢ ball (0 : ℂ) ρ))
    (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (hsq : ∀ p ∈ univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (hdec : ExpDecayCInftyTube (fd Jbar Jinf) ρ b) (τ : ℝ) :
    Tinf Jinf τ = (-Complex.I) • Minf Jinf τ := by
  have hO : IsOpen (ball (0 : ℂ) ρ) := isOpen_ball
  have hdiff : ∀ w ∈ ball (0 : ℂ) ρ, DifferentiableAt ℝ (fun w : ℂ => Jinf (τ, w)) w := by
    intro w hw
    have h1 : ContDiffOn ℝ ∞ (fun w : ℂ => Jinf (τ, w)) (ball (0 : ℂ) ρ) :=
      hJi.comp (contDiffOn_const.prodMk contDiffOn_id) fun w hw => ⟨mem_univ _, hw⟩
    exact (h1.contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp)
  have d0 := hdiff 0 (mem_ball_self hρ)
  -- `w ↦ Jinf(τ,w) ∘ Jinf(τ,w)` is constant near `0`
  have hconst : (fun w : ℂ => (Jinf (τ, w)).comp (Jinf (τ, w))) =ᶠ[𝓝 0]
      fun _ => -ContinuousLinearMap.id ℝ (ℂ × ℂ) :=
    Filter.eventually_of_mem (hO.mem_nhds (mem_ball_self hρ)) fun w hw => Jinf_sq hb hsq hdec τ hw
  have hD : fderiv ℝ (fun w : ℂ => (Jinf (τ, w)).comp (Jinf (τ, w))) 0 = 0 := by
    rw [hconst.fderiv_eq]; simp
  rw [fderiv_clm_comp d0 d0, Jinf_zero hb hρ h0 hdec τ] at hD
  ext1 a
  have hDa := congrArg (fun L : ℂ →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ) => L a ((1 : ℂ), (0 : ℂ))) hD
  simp only [add_apply, coe_comp', Function.comp_apply, zero_apply] at hDa
  have hj1 : jStd ((1 : ℂ), (0 : ℂ)) = (Complex.I, 0) := by simp [jStd]
  have hjv : ∀ v : ℂ × ℂ, (jStd v).2 = Complex.I * v.2 := by intro v; simp [jStd]
  simp only [compL_apply, flip_apply, comp_apply, hj1] at hDa
  have h2 := congrArg Prod.snd hDa
  simp only [Prod.snd_add, Prod.snd_zero, hjv] at h2
  simp only [Tinf, Minf, comp_apply, apply_apply, coe_snd', smul_apply, smul_eq_mul]
  rw [Kd]
  linear_combination h2

end

end FiniteEnergyPlane.B3E

/-! B3E layer L: derivative bounds and Lipschitz bounds for functions on `ℝ × ℂ` that are
`1`-periodic in the first variable, on a strip `ℝ × closedBall 0 r`. -/

namespace FiniteEnergyPlane.B3E


open Metric Filter Topology Set
open scoped ContDiff

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma per_int (Φ : ℝ × ℂ → F) (hper : ∀ τ w, Φ (τ + 1, w) = Φ (τ, w)) (n : ℤ) :
    (fun x : ℝ × ℂ => Φ (x + ((n : ℝ), (0 : ℂ)))) = Φ := by
  funext x
  have hP : Function.Periodic (fun τ => Φ (τ, x.2)) 1 := fun τ => hper τ x.2
  have e : x + ((n : ℝ), (0 : ℂ)) = (x.1 + (n : ℝ), x.2) := by ext <;> simp
  rw [e]
  have := (hP.int_mul n) x.1
  simpa using this

lemma per_bound (Φ : ℝ × ℂ → F) {r ρ : ℝ} (hrρ : r < ρ)
    (hΦ : ContDiffOn ℝ ∞ Φ (univ ×ˢ ball (0 : ℂ) ρ)) (hper : ∀ τ w, Φ (τ + 1, w) = Φ (τ, w))
    (n : ℕ) : ∃ C : ℝ, ∀ τ : ℝ, ∀ w ∈ closedBall (0 : ℂ) r, ∀ i ≤ n,
      ‖iteratedFDeriv ℝ i Φ (τ, w)‖ ≤ C := by
  have hO : IsOpen (univ ×ˢ ball (0 : ℂ) ρ) := (isOpen_univ : IsOpen (univ : Set ℝ)).prod isOpen_ball
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) r) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKs : Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) r ⊆ univ ×ˢ ball (0 : ℂ) ρ :=
    prod_mono (subset_univ _) (closedBall_subset_ball hrρ)
  have hc : ∀ i : ℕ, ContinuousOn (iteratedFDeriv ℝ i Φ) (univ ×ˢ ball (0 : ℂ) ρ) := by
    intro i
    have := hΦ.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast le_top)
      hO.uniqueDiffOn
    exact this.congr fun x hx => (iteratedFDerivWithin_of_isOpen i hO hx).symm
  choose C hC using fun i : ℕ => hK.exists_bound_of_continuousOn ((hc i).mono hKs)
  refine ⟨∑ i ∈ Finset.range (n + 1), |C i|, fun τ w hw i hi => ?_⟩
  have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  set k : ℤ := ⌊τ⌋
  have hx : (Int.fract τ, w) ∈ Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) r :=
    ⟨⟨Int.fract_nonneg τ, (Int.fract_lt_one τ).le⟩, hw⟩
  have heq : iteratedFDeriv ℝ i Φ (τ, w) = iteratedFDeriv ℝ i Φ (Int.fract τ, w) := by
    have h1 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := Φ) i ((k : ℝ), (0 : ℂ))
      (x := (Int.fract τ, w))
    rw [per_int Φ hper k] at h1
    rw [h1]
    congr 1
    ext
    · simp only [Prod.fst_add, k, Int.fract_add_floor]
    · simp
  rw [heq]
  exact (hC i _ hx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) hmem))

lemma per_lip (Φ : ℝ × ℂ → F) {r ρ : ℝ} (hrρ : r < ρ)
    (hΦ : ContDiffOn ℝ ∞ Φ (univ ×ˢ ball (0 : ℂ) ρ)) (hper : ∀ τ w, Φ (τ + 1, w) = Φ (τ, w)) :
    ∃ L : ℝ, ∀ p q : ℝ × ℂ, ‖p.2‖ ≤ r → ‖q.2‖ ≤ r → ‖Φ p - Φ q‖ ≤ L * ‖p - q‖ := by
  obtain ⟨C, hC⟩ := per_bound Φ hrρ hΦ hper 1
  have hO : IsOpen (univ ×ˢ ball (0 : ℂ) ρ) := (isOpen_univ : IsOpen (univ : Set ℝ)).prod isOpen_ball
  have hconv : Convex ℝ ((univ : Set ℝ) ×ˢ closedBall (0 : ℂ) r) :=
    (convex_univ : Convex ℝ (univ : Set ℝ)).prod (convex_closedBall _ _)
  refine ⟨C, fun p q hp hq => ?_⟩
  have hsub : (univ : Set ℝ) ×ˢ closedBall (0 : ℂ) r ⊆ univ ×ˢ ball (0 : ℂ) ρ :=
    prod_mono (subset_refl (univ : Set ℝ)) (closedBall_subset_ball hrρ)
  have hd : ∀ x ∈ (univ : Set ℝ) ×ˢ closedBall (0 : ℂ) r, DifferentiableAt ℝ Φ x := fun x hx =>
    ((hΦ.contDiffAt (hO.mem_nhds (hsub hx))).differentiableAt (by simp))
  have hb : ∀ x ∈ (univ : Set ℝ) ×ˢ closedBall (0 : ℂ) r, ‖fderiv ℝ Φ x‖ ≤ C := by
    intro x hx
    rw [← norm_iteratedFDeriv_one]
    exact hC x.1 x.2 hx.2 1 le_rfl
  have := hconv.norm_image_sub_le_of_norm_fderiv_le hd hb
    (show q ∈ (univ : Set ℝ) ×ˢ closedBall (0 : ℂ) r from ⟨mem_univ _, mem_closedBall_zero_iff.2 hq⟩)
    (show p ∈ (univ : Set ℝ) ×ˢ closedBall (0 : ℂ) r from ⟨mem_univ _, mem_closedBall_zero_iff.2 hp⟩)
  simpa using this

end

end FiniteEnergyPlane.B3E

/-! B3E layer H: bounded-derivative calculus for functions smooth on a half-plane
`Ioi s₀ ×ˢ univ`, and decay of bilinear images. -/

namespace FiniteEnergyPlane.B3E


open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Real Nat

noncomputable section

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Smooth on a half-plane, all derivatives bounded far out. -/
def BdH (f : ℝ × ℝ → F) : Prop :=
  (∃ s₀ : ℝ, ContDiffOn ℝ ∞ f (Ioi s₀ ×ˢ univ)) ∧ Bd f

lemma hp_open (s₀ : ℝ) : IsOpen (Ioi s₀ ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ

lemma hp_mono {s₀ s₁ : ℝ} (h : s₀ ≤ s₁) : Ioi s₁ ×ˢ (univ : Set ℝ) ⊆ Ioi s₀ ×ˢ univ :=
  prod_mono (Ioi_subset_Ioi h) le_rfl

lemma contDiffAt_hp {f : ℝ × ℝ → F} {s₀ : ℝ} (hf : ContDiffOn ℝ ∞ f (Ioi s₀ ×ˢ univ))
    {s : ℝ} (hs : s₀ < s) (t : ℝ) (n : ℕ) : ContDiffAt ℝ n f (s, t) :=
  ((hf.contDiffAt ((hp_open s₀).mem_nhds
    (show ((s, t) : ℝ × ℝ) ∈ Ioi s₀ ×ˢ univ from ⟨hs, mem_univ t⟩)))).of_le
    (by exact_mod_cast le_top)

lemma BdH.upTo {f : ℝ × ℝ → F} (hf : BdH f) (k : ℕ) :
    ∃ B T : ℝ, 0 ≤ B ∧ ∀ i ≤ k, ∀ s ≥ T, ∀ t : ℝ, ‖iteratedFDeriv ℝ i f (s, t)‖ ≤ B :=
  hf.2.upTo k

lemma BdH.of_contDiff {f : ℝ × ℝ → F} (hf : ContDiff ℝ ∞ f) (hb : Bd f) : BdH f :=
  ⟨⟨0, hf.contDiffOn⟩, hb⟩

lemma bdH_const (c : F) : BdH (fun _ : ℝ × ℝ => c) := .of_contDiff contDiff_const (bd_const c)

lemma bdH_of_expDecay {f : ℝ × ℝ → F} {b : ℝ} (hb : 0 ≤ b) (hf : ExpDecayCInfty f b) : BdH f :=
  ⟨hf.1, bd_of_expDecay hb hf⟩

lemma bdH_add {f g : ℝ × ℝ → F} (hf : BdH f) (hg : BdH g) : BdH (fun p => f p + g p) := by
  obtain ⟨⟨s₁, hf1⟩, hbf⟩ := hf
  obtain ⟨⟨s₂, hg1⟩, hbg⟩ := hg
  refine ⟨⟨max s₁ s₂, (hf1.mono (hp_mono (le_max_left _ _))).add
    (hg1.mono (hp_mono (le_max_right _ _)))⟩, fun m => ?_⟩
  obtain ⟨C₁, a₁, h₁⟩ := hbf m
  obtain ⟨C₂, a₂, h₂⟩ := hbg m
  refine ⟨C₁ + C₂, max (max a₁ a₂) (max s₁ s₂ + 1), fun s hs t => ?_⟩
  have ha := le_of_max_le_left hs
  have hs' : max s₁ s₂ < s := by linarith [le_of_max_le_right hs]
  rw [show (fun p => f p + g p) = f + g from rfl,
    iteratedFDeriv_add_apply (contDiffAt_hp hf1 (lt_of_le_of_lt (le_max_left _ _) hs') t m)
      (contDiffAt_hp hg1 (lt_of_le_of_lt (le_max_right _ _) hs') t m)]
  exact (norm_add_le _ _).trans (add_le_add (h₁ s (le_of_max_le_left ha) t)
    (h₂ s (le_of_max_le_right ha) t))

lemma bdH_neg {f : ℝ × ℝ → F} (hf : BdH f) : BdH (fun p => -f p) := by
  obtain ⟨⟨s₁, hf1⟩, hbf⟩ := hf
  exact ⟨⟨s₁, hf1.neg⟩, bd_neg hbf⟩

lemma bdH_sub {f g : ℝ × ℝ → F} (hf : BdH f) (hg : BdH g) : BdH (fun p => f p - g p) := by
  simpa [sub_eq_add_neg] using bdH_add hf (bdH_neg hg)

/-- Leibniz bound on the half-plane. -/
lemma norm_bilin_hp (B : F →L[ℝ] G →L[ℝ] H) {f : ℝ × ℝ → F} {g : ℝ × ℝ → G} {s₀ : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi s₀ ×ˢ univ)) (hg : ContDiffOn ℝ ∞ g (Ioi s₀ ×ˢ univ))
    {s : ℝ} (hs : s₀ < s) (t : ℝ) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun p => B (f p) (g p)) (s, t)‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f (s, t)‖ * ‖iteratedFDeriv ℝ (m - i) g (s, t)‖ := by
  have hU := hp_open s₀
  have hx : ((s, t) : ℝ × ℝ) ∈ Ioi s₀ ×ˢ univ := ⟨hs, mem_univ t⟩
  have key := B.norm_iteratedFDerivWithin_le_of_bilinear hf hg hU.uniqueDiffOn hx
    (n := m) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen m hU hx] at key
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hx] using key

lemma bdH_bilin (B : F →L[ℝ] G →L[ℝ] H) {f : ℝ × ℝ → F} {g : ℝ × ℝ → G}
    (hf : BdH f) (hg : BdH g) : BdH (fun p => B (f p) (g p)) := by
  obtain ⟨⟨s₁, hf1⟩, hbf⟩ := hf
  obtain ⟨⟨s₂, hg1⟩, hbg⟩ := hg
  set s₀ := max s₁ s₂
  have hf0 := hf1.mono (hp_mono (le_max_left s₁ s₂))
  have hg0 := hg1.mono (hp_mono (le_max_right s₁ s₂))
  refine ⟨⟨s₀, (B.contDiff.comp_contDiffOn hf0).clm_apply hg0⟩, fun m => ?_⟩
  obtain ⟨B₁, T₁, hB₁, h₁⟩ := hbf.upTo m
  obtain ⟨B₂, T₂, hB₂, h₂⟩ := hbg.upTo m
  refine ⟨‖B‖ * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B₁ * B₂,
    max (max T₁ T₂) (s₀ + 1), fun s hs t => ?_⟩
  have hT := le_of_max_le_left hs
  have hs0 : s₀ < s := by linarith [le_of_max_le_right hs]
  refine (norm_bilin_hp B hf0 hg0 hs0 t m).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by positivity)
  have e1 := h₁ i (by simpa [Nat.lt_succ_iff] using hi) s (le_of_max_le_left hT) t
  have e2 := h₂ (m - i) (Nat.sub_le _ _) s (le_of_max_le_right hT) t
  exact mul_le_mul (mul_le_mul_of_nonneg_left e1 (Nat.cast_nonneg _)) e2 (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hB₁)

lemma bdH_clm (L : F →L[ℝ] G) {f : ℝ × ℝ → F} (hf : BdH f) : BdH (fun p => L (f p)) := by
  obtain ⟨⟨s₁, hf1⟩, hbf⟩ := hf
  refine ⟨⟨s₁, L.contDiff.comp_contDiffOn hf1⟩, fun m => ?_⟩
  obtain ⟨C, a, h⟩ := hbf m
  refine ⟨‖L‖ * C, max a (s₁ + 1), fun s hs t => ?_⟩
  have hs1 : s₁ < s := by linarith [le_of_max_le_right hs]
  rw [show (fun p => L (f p)) = L ∘ f from rfl,
    L.iteratedFDeriv_comp_left (contDiffAt_hp hf1 hs1 t m) le_rfl]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_left (h s (le_of_max_le_left hs) t) (norm_nonneg _))

/-- Bilinear image of a decaying and a bounded family decays at the same rate. -/
lemma expDecay_bilin (B : F →L[ℝ] G →L[ℝ] H) {f : ℝ × ℝ → F} {g : ℝ × ℝ → G} {b : ℝ}
    (hf : ExpDecayCInfty f b) (hg : BdH g) : ExpDecayCInfty (fun p => B (f p) (g p)) b := by
  obtain ⟨⟨s₁, hf1⟩, hdf⟩ := hf
  obtain ⟨⟨s₂, hg1⟩, hbg⟩ := hg
  set s₀ := max s₁ s₂
  have hf0 := hf1.mono (hp_mono (le_max_left s₁ s₂))
  have hg0 := hg1.mono (hp_mono (le_max_right s₁ s₂))
  refine ⟨⟨s₀, (B.contDiff.comp_contDiffOn hf0).clm_apply hg0⟩, fun m => ?_⟩
  choose Ci si hCi using hdf
  obtain ⟨B₂, T₂, hB₂, h₂⟩ := hbg.upTo m
  set A := ∑ i ∈ Finset.range (m + 1), |Ci i|
  set T := ∑ i ∈ Finset.range (m + 1), |si i|
  refine ⟨‖B‖ * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A * B₂,
    max (max T T₂) (s₀ + 1), fun s hs t => ?_⟩
  have hT := le_of_max_le_left hs
  have hs0 : s₀ < s := by linarith [le_of_max_le_right hs]
  refine (norm_bilin_hp B hf0 hg0 hs0 t m).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hmem : i ∈ Finset.range (m + 1) := hi
  have hsi : si i ≤ s := (le_abs_self _).trans ((Finset.single_le_sum (f := fun i => |si i|)
    (fun _ _ => abs_nonneg _) hmem).trans (le_of_max_le_left hT))
  have e1 : ‖iteratedFDeriv ℝ i f (s, t)‖ ≤ A * Real.exp (-(b * s)) :=
    (hCi i s hsi t).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Ci i|) (fun _ _ => abs_nonneg _) hmem))
      (Real.exp_pos _).le)
  have e2 := h₂ (m - i) (Nat.sub_le _ _) s (le_of_max_le_right hT) t
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc ‖B‖ * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f (s, t)‖ *
        ‖iteratedFDeriv ℝ (m - i) g (s, t)‖)
      ≤ ‖B‖ * ((m.choose i : ℝ) * (A * Real.exp (-(b * s))) * B₂) := by
        gcongr
    _ = ‖B‖ * ((m.choose i : ℝ) * A * B₂) * Real.exp (-(b * s)) := by ring

lemma expDecay_bilin' (B : F →L[ℝ] G →L[ℝ] H) {f : ℝ × ℝ → F} {g : ℝ × ℝ → G} {b : ℝ}
    (hf : BdH f) (hg : ExpDecayCInfty g b) : ExpDecayCInfty (fun p => B (f p) (g p)) b :=
  expDecay_bilin B.flip hg hf

lemma expDecay_add {f g : ℝ × ℝ → F} {b : ℝ} (hf : ExpDecayCInfty f b)
    (hg : ExpDecayCInfty g b) : ExpDecayCInfty (fun p => f p + g p) b := by
  obtain ⟨⟨s₁, hf1⟩, hdf⟩ := hf
  obtain ⟨⟨s₂, hg1⟩, hdg⟩ := hg
  refine ⟨⟨max s₁ s₂, (hf1.mono (hp_mono (le_max_left _ _))).add
    (hg1.mono (hp_mono (le_max_right _ _)))⟩, fun m => ?_⟩
  obtain ⟨C₁, a₁, h₁⟩ := hdf m
  obtain ⟨C₂, a₂, h₂⟩ := hdg m
  refine ⟨C₁ + C₂, max (max a₁ a₂) (max s₁ s₂ + 1), fun s hs t => ?_⟩
  have ha := le_of_max_le_left hs
  have hs' : max s₁ s₂ < s := by linarith [le_of_max_le_right hs]
  rw [show (fun p => f p + g p) = f + g from rfl,
    iteratedFDeriv_add_apply (contDiffAt_hp hf1 (lt_of_le_of_lt (le_max_left _ _) hs') t m)
      (contDiffAt_hp hg1 (lt_of_le_of_lt (le_max_right _ _) hs') t m), add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h₁ s (le_of_max_le_left ha) t)
    (h₂ s (le_of_max_le_right ha) t))

lemma expDecay_neg {f : ℝ × ℝ → F} {b : ℝ} (hf : ExpDecayCInfty f b) :
    ExpDecayCInfty (fun p => -f p) b := by
  obtain ⟨⟨s₁, hf1⟩, hdf⟩ := hf
  refine ⟨⟨s₁, hf1.neg⟩, fun m => ?_⟩
  obtain ⟨C, a, h⟩ := hdf m
  exact ⟨C, a, fun s hs t => by
    rw [show (fun p => -f p) = -f from rfl, iteratedFDeriv_neg_apply, norm_neg]; exact h s hs t⟩

lemma expDecay_sub {f g : ℝ × ℝ → F} {b : ℝ} (hf : ExpDecayCInfty f b)
    (hg : ExpDecayCInfty g b) : ExpDecayCInfty (fun p => f p - g p) b := by
  simpa [sub_eq_add_neg] using expDecay_add hf (expDecay_neg hg)

lemma expDecay_clm (L : F →L[ℝ] G) {f : ℝ × ℝ → F} {b : ℝ} (hf : ExpDecayCInfty f b) :
    ExpDecayCInfty (fun p => L (f p)) b := by
  obtain ⟨⟨s₁, hf1⟩, hdf⟩ := hf
  refine ⟨⟨s₁, L.contDiff.comp_contDiffOn hf1⟩, fun m => ?_⟩
  obtain ⟨C, a, h⟩ := hdf m
  refine ⟨‖L‖ * C, max a (s₁ + 1), fun s hs t => ?_⟩
  have hs1 : s₁ < s := by linarith [le_of_max_le_right hs]
  rw [show (fun p => L (f p)) = L ∘ f from rfl,
    L.iteratedFDeriv_comp_left (contDiffAt_hp hf1 hs1 t m) le_rfl, mul_assoc]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_left (h s (le_of_max_le_left hs) t) (norm_nonneg _))

/-- Interpolation for half-plane smooth functions. -/
lemma expDecay_of_bdH {f : ℝ × ℝ → F} (hf : BdH f) {b C s₀ : ℝ}
    (h0 : ∀ s ≥ s₀, ∀ t : ℝ, ‖f (s, t)‖ ≤ C * Real.exp (-(b * s))) (hb : 0 < b) :
    ∀ b' < b, ExpDecayCInfty f b' := by
  obtain ⟨⟨s₁, hf1⟩, hbf⟩ := hf
  have hT : TendstoZeroUnif f := by
    intro ε hε
    have ht : Tendsto (fun s : ℝ => C * Real.exp (-(b * s))) atTop (𝓝 0) := by
      have : Tendsto (fun s : ℝ => Real.exp (-(b * s))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
          (tendsto_id.const_mul_atTop hb))
      simpa using this.const_mul C
    obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 ((ht.eventually (ge_mem_nhds hε)).and
      (eventually_ge_atTop s₀))
    exact ⟨s₂, fun s hs t => (h0 s (hs₂ s hs).2 t).trans (hs₂ s hs).1⟩
  have hZ := tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd f s₁ hf1 hT hbf
  exact expDecayCInfty_of_tendstoZeroCInfty f hZ b C s₀ h0

end

end FiniteEnergyPlane.B3E

/-! B3E layer S1: decay of the normal structure along the graph at `∞`, and of the frames. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real Nat

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Composition bounds with thresholds depending on the order -/

lemma bd_comp_hp {ι : Type*} (Φ : E → F) (V : Set E) (hV : IsOpen V) (hΦ : ContDiffOn ℝ ∞ Φ V)
    (X : ι → ℝ × ℝ → E) (a : ℝ) (hX : ∀ θ, ContDiffOn ℝ ∞ (X θ) (Ioi a ×ˢ univ))
    (hXV : ∀ θ, ∀ s > a, ∀ t, X θ (s, t) ∈ V)
    (hb : ∀ n : ℕ, ∃ C D s₁ : ℝ, ∀ θ, ∀ s ≥ s₁, ∀ t,
      (∀ i ≤ n, ‖iteratedFDeriv ℝ i Φ (X θ (s, t))‖ ≤ C) ∧
      ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (X θ) (s, t)‖ ≤ D) :
    ∀ n : ℕ, ∃ K s₁ : ℝ, ∀ θ, ∀ s ≥ s₁, ∀ t,
      ‖iteratedFDeriv ℝ n (fun p => Φ (X θ p)) (s, t)‖ ≤ K := by
  intro n
  obtain ⟨C, D, s₁, h⟩ := hb n
  refine ⟨n ! * C * (max 1 D) ^ n, max s₁ (a + 1), fun θ s hs t => ?_⟩
  have hs1 : s₁ ≤ s := le_of_max_le_left hs
  have hsa : a < s := by linarith [le_of_max_le_right hs]
  refine BT.fdb (q := (s, t)) (hp_open a) hV hΦ (hX θ) (fun q hq => ?_)
    (show ((s, t) : ℝ × ℝ) ∈ Ioi a ×ˢ univ from ⟨hsa, mem_univ t⟩)
    (fun i hi => (h θ s hs1 t).1 i hi) (fun i hi1 hi => ?_)
  · obtain ⟨hq1, -⟩ := hq
    simpa using hXV θ q.1 hq1 q.2
  · refine ((h θ s hs1 t).2 i hi1 hi).trans ((le_max_right 1 D).trans ?_)
    exact le_self_pow₀ (le_max_left 1 D) (by omega)

lemma norm_iteratedFDeriv_affine_le (L : ℝ × ℝ →L[ℝ] E) (c : E) (x : ℝ × ℝ) {i : ℕ}
    (hi : 1 ≤ i) : ‖iteratedFDeriv ℝ i (fun q => L q + c) x‖ ≤ ‖L‖ := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hd : fderiv ℝ (fun q => L q + c) = fun _ => L := funext fun y => by
    rw [fderiv_add_const]; exact L.fderiv
  rw [← norm_iteratedFDeriv_fderiv, hd]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne hj.ne']; simp

lemma norm_iteratedFDeriv_affine_add_le (L : ℝ × ℝ →L[ℝ] E) (c : E) (y : ℝ × ℝ → E) {a : ℝ}
    (hy : ContDiffOn ℝ ∞ y (Ioi a ×ˢ univ)) {s : ℝ} (hs : a < s) (t : ℝ) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun q => L q + c + y q) (s, t)‖ ≤
      ‖L‖ + ‖iteratedFDeriv ℝ i y (s, t)‖ := by
  have e : (fun q => L q + c + y q) = (fun q => L q + c) + y := rfl
  rw [e, iteratedFDeriv_add_apply ((L.contDiff (n := i)).add contDiff_const).contDiffAt
    (contDiffAt_hp hy hs t i)]
  exact (norm_add_le _ _).trans (by linarith [norm_iteratedFDeriv_affine_le L c (s, t) hi])

/-! ### `cylJ` on `ℝ × ℝ × ℂ` -/

/-- `cylJ` as a function of one variable. -/
def Fc (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (r : ℝ × ℝ × ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  cylJ Jbar r.1 r.2.1 r.2.2

variable {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
  {Sinf : ℝ → Mat 1}

lemma Fc_contDiffOn (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf) :
    ∃ s₀ : ℝ, ContDiffOn ℝ ∞ (Fc Jbar) (Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) := by
  obtain ⟨-, -, -, hJ, -, ⟨⟨s₀, hD⟩, -⟩, -, -⟩ := hT
  refine ⟨s₀, ?_⟩
  set π₂ : ℝ × ℝ × ℂ →L[ℝ] ℝ × ℂ := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)
  have hsplit : Fc Jbar = (fun q : ℝ × ℝ × ℂ => cylJ Jbar q.1 q.2.1 q.2.2 - Jinf (q.2.1, q.2.2)) +
      Jinf ∘ π₂ := by
    funext q; simp [π₂, Fc]
  rw [hsplit]
  refine hD.add (hJ.comp π₂.contDiff.contDiffOn fun q hq => ?_)
  exact ⟨mem_univ _, hq.2.2⟩

lemma Fc_lip (hρ : 0 < ρ) (hb : 0 < b) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf) :
    ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ∀ w ∈ closedBall (0 : ℂ) (ρ / 2),
      ‖cylJ Jbar s t w - jStd‖ ≤ C * ‖w‖ := by
  obtain ⟨C, s₁, hC⟩ := cylJ_iteratedFDeriv_bdd ρ b hρ hb Jbar Jinf Sinf hT 1
  obtain ⟨s₀, hs₀⟩ := Fc_contDiffOn hT
  have h0 := hT.2.2.1
  refine ⟨C, max s₁ (s₀ + 1), fun s hs t w hw => ?_⟩
  have hs1 : s₁ ≤ s := le_trans (le_max_left _ _) hs
  have hs0 : s₀ < s := by have := le_trans (le_max_right _ _) hs; linarith
  set L : ℂ →L[ℝ] ℝ × ℝ × ℂ :=
    (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℂ)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) with hL
  have hL1 : ‖L‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_one₀ (ContinuousLinearMap.norm_inr_le_one ℝ ℝ (ℝ × ℂ)) (norm_nonneg _)
      (ContinuousLinearMap.norm_inr_le_one ℝ ℝ ℂ)
  have hpath : ∀ v : ℂ, ((s, t, 0) : ℝ × ℝ × ℂ) + L v = (s, t, v) := by
    intro v; simp [hL]
  have hO : IsOpen (Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ) :=
    isOpen_Ioi.prod ((isOpen_univ (X := ℝ)).prod (isOpen_ball (x := (0 : ℂ))))
  have hder : ∀ v ∈ closedBall (0 : ℂ) (ρ / 2),
      HasFDerivWithinAt (fun v => cylJ Jbar s t v) ((fderiv ℝ (Fc Jbar) (s, t, v)).comp L)
        (closedBall (0 : ℂ) (ρ / 2)) v := by
    intro v hv
    have hvρ : v ∈ ball (0 : ℂ) ρ := closedBall_subset_ball (by linarith) hv
    have hFd : HasFDerivAt (Fc Jbar) (fderiv ℝ (Fc Jbar) (s, t, v)) ((s, t, 0) + L v) := by
      rw [hpath]
      exact ((hs₀.contDiffAt (hO.mem_nhds (show ((s, t, v) : ℝ × ℝ × ℂ) ∈
        Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ from ⟨hs0, mem_univ _, hvρ⟩))).differentiableAt
        (by simp)).hasFDerivAt
    have hg : HasFDerivAt (fun v : ℂ => ((s, t, 0) : ℝ × ℝ × ℂ) + L v) L v :=
      L.hasFDerivAt.const_add _
    have := hFd.comp v hg
    refine (this.congr_of_eventuallyEq ?_).hasFDerivWithinAt
    exact Eventually.of_forall fun v' => by simp [Fc, hpath]
  have hbound : ∀ v ∈ closedBall (0 : ℂ) (ρ / 2),
      ‖(fderiv ℝ (Fc Jbar) (s, t, v)).comp L‖ ≤ C := by
    intro v hv
    have h1 := hC s hs1 t v hv
    rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] at h1
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖fderiv ℝ (Fc Jbar) (s, t, v)‖ * ‖L‖ ≤ ‖fderiv ℝ (Fc Jbar) (s, t, v)‖ * 1 :=
          mul_le_mul_of_nonneg_left hL1 (ContinuousLinearMap.opNorm_nonneg _)
      _ ≤ C := by rw [mul_one]; exact h1
  have key := (convex_closedBall (0 : ℂ) (ρ / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hder hbound (mem_closedBall_self (by linarith)) hw
  rw [cylJ_zero h0, sub_zero] at key
  exact key

/-- Derivative bounds of `cylJ` far out, uniformly up to order `n`, on `closedBall 0 (ρ/2)`. -/
lemma Fc_bound_upTo (hρ : 0 < ρ) (hb : 0 < b) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (n : ℕ) : ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ∀ w ∈ closedBall (0 : ℂ) (ρ / 2), ∀ i ≤ n,
      ‖iteratedFDeriv ℝ i (Fc Jbar) (s, t, w)‖ ≤ C := by
  choose Ci si hCi using fun i => cylJ_iteratedFDeriv_bdd ρ b hρ hb Jbar Jinf Sinf hT i
  refine ⟨∑ i ∈ Finset.range (n + 1), |Ci i|, ∑ i ∈ Finset.range (n + 1), |si i|,
    fun s hs t w hw i hi => ?_⟩
  have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have hsi : si i ≤ s := (le_abs_self _).trans ((Finset.single_le_sum (f := fun i => |si i|)
    (fun _ _ => abs_nonneg _) hmem).trans hs)
  exact (hCi i s hsi t w hw).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |Ci i|) (fun _ _ => abs_nonneg _) hmem))

/-! ### The normal structure along the graph, in cylindrical coordinates -/

/-- `u ↦ (re u, im u)`. -/
def cToR : ℂ →L[ℝ] ℝ × ℝ := Complex.reCLM.prod Complex.imCLM

lemma fderiv_gc_apply {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (q : ℝ × ℝ) (u : ℂ) :
    fderiv ℝ (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) q (cToR u) =
      fderiv ℝ g (cylInf q.1 q.2) (lam q.1 q.2 * u) := by
  obtain ⟨L, hL, hL1, hL2⟩ := cyl_hasFDerivAt q
  have hgd := ((hg.differentiable (by simp)) (cylInf q.1 q.2)).hasFDerivAt
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => g (cylInf p.1 p.2))
      ((fderiv ℝ g (cylInf q.1 q.2)).comp L) q := hgd.comp q hL
  rw [h2.fderiv]
  have e : cToR u = u.re • ((1 : ℝ), (0 : ℝ)) + u.im • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp [cToR]
  have hLu : L (cToR u) = lam q.1 q.2 * u := by
    rw [e, map_add, map_smul, map_smul, hL1, hL2]
    conv_rhs => rw [← Complex.re_add_im u]
    simp only [lam, Complex.real_smul]
    ring
  simp only [comp_apply, hLu]

variable {β : ContDiffBump (0 : ℂ)} {g : ℂ → ℂ}

lemma C0_cyl {r₁ : ℝ} (hβ : r₁ ≤ β.rIn) (hgr : ∀ x, ‖g x‖ ≤ r₁) (hg : ContDiff ℝ ∞ g)
    (q : ℝ × ℝ) :
    C0 Jbar β g (cylInf q.1 q.2) 1 =
      J22 (cylJ Jbar q.1 q.2 (g (cylInf q.1 q.2))) 1 -
        fderiv ℝ (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) q
          (cToR (J12 (cylJ Jbar q.1 q.2 (g (cylInf q.1 q.2))) 1)) := by
  rw [fderiv_gc_apply hg]
  show Bblk (Jt Jbar β (cylInf q.1 q.2, g (cylInf q.1 q.2) + 0))
    (fderiv ℝ g (cylInf q.1 q.2)) 1 = _
  rw [Jt_graph hβ hgr, Bblk_cyl Jbar q.1 q.2]
  simp [Bblk, mulL_apply]

/-- `J ↦ (J (0, 1)).2`. -/
def ev22 : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.snd ℝ ℂ ℂ).comp (ContinuousLinearMap.apply ℝ (ℂ × ℂ) ((0 : ℂ), (1 : ℂ)))

/-- `J ↦ (re, im) of (J (0, 1)).1`. -/
def ev12 : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] ℝ × ℝ :=
  cToR.comp ((ContinuousLinearMap.fst ℝ ℂ ℂ).comp
    (ContinuousLinearMap.apply ℝ (ℂ × ℂ) ((0 : ℂ), (1 : ℂ))))

lemma ev22_apply (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) : ev22 J = J22 J 1 := by simp [ev22, J22]

lemma ev12_apply (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) : ev12 J = cToR (J12 J 1) := by simp [ev12, J12]

/-- The inner map `q ↦ (q, ĝ q)`. -/
def Yg (g : ℂ → ℂ) (q : ℝ × ℝ) : ℝ × ℝ × ℂ := (q.1, q.2, g (cylInf q.1 q.2))

/-- `q ↦ (q.1, q.2, 0)`. -/
def L3 : ℝ × ℝ →L[ℝ] ℝ × ℝ × ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0)

/-- `w ↦ (0, 0, w)`. -/
def I3 : ℂ →L[ℝ] ℝ × ℝ × ℂ :=
  (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℂ)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)

lemma Yg_eq (g : ℂ → ℂ) : Yg g = fun q => L3 q + 0 + I3 (g (cylInf q.1 q.2)) := by
  funext q; simp [Yg, L3, I3]

/-- `ĝ` decays, so it is eventually in `closedBall 0 r` for any `r > 0`. -/
lemma eventually_norm_le {f : ℝ × ℝ → F} {b' : ℝ} (hb' : 0 < b') (hf : ExpDecayCInfty f b')
    {r : ℝ} (hr : 0 < r) : ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t, ‖f (s, t)‖ ≤ r := by
  obtain ⟨C, s₁, hC⟩ := hf.2 0
  have ht : Tendsto (fun s : ℝ => C * Real.exp (-(b' * s))) atTop (𝓝 0) := by
    have : Tendsto (fun s : ℝ => Real.exp (-(b' * s))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop hb'))
    simpa using this.const_mul C
  obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 ((ht.eventually (ge_mem_nhds hr)).and
    (eventually_ge_atTop s₁))
  refine ⟨s₂, fun s hs t => ?_⟩
  have := hC s (hs₂ s hs).2 t
  rw [norm_iteratedFDeriv_zero] at this
  exact this.trans (hs₂ s hs).1

/-- `BdH` of `q ↦ cylJ(q, ĝ q)`. -/
lemma bdH_Fc_Yg (hρ : 0 < ρ) (hb : 0 < b) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    {r₁ : ℝ} (hr₁ : r₁ < ρ) (hgr : ∀ x, ‖g x‖ ≤ r₁) (hg : ContDiff ℝ ∞ g) {b' : ℝ}
    (hb' : 0 < b') (hgas : ExpDecayCInfty (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) b') :
    BdH (fun q => Fc Jbar (Yg g q)) := by
  obtain ⟨s₀, hFc⟩ := Fc_contDiffOn hT
  have hgc : ContDiff ℝ ∞ (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) := hg.comp cyl_contDiff
  have hY : ContDiff ℝ ∞ (Yg g) := by
    rw [Yg_eq]; exact (L3.contDiff.add contDiff_const).add (I3.contDiff.comp hgc)
  have hmaps : ∀ s > s₀, ∀ t, Yg g (s, t) ∈ Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ :=
    fun s hs t => ⟨hs, mem_univ _, mem_ball_zero_iff.2 ((hgr _).trans_lt hr₁)⟩
  have hO : IsOpen (Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ) :=
    isOpen_Ioi.prod ((isOpen_univ (X := ℝ)).prod (isOpen_ball (x := (0 : ℂ))))
  refine ⟨⟨s₀, hFc.comp hY.contDiffOn fun q hq => hmaps q.1 hq.1 q.2⟩, ?_⟩
  obtain ⟨s₂, hs₂⟩ := eventually_norm_le hb' hgas (half_pos hρ)
  have key := bd_comp_hp (ι := Unit) (Fc Jbar) _ hO hFc (fun _ => Yg g) s₀
    (fun _ => hY.contDiffOn) (fun _ => hmaps) (fun n => by
      obtain ⟨C, s₁, hC⟩ := Fc_bound_upTo hρ hb hT n
      obtain ⟨B, T, -, hB⟩ := BT.bound_of_expDecay hb'.le hgas n
      refine ⟨C, ‖L3‖ + ‖I3‖ * B, max (max s₁ s₂) (max T (s₀ + 1)),
        fun _ s hs t => ⟨fun i hi => ?_, fun i hi1 hi => ?_⟩⟩
      · exact hC s (le_trans (le_max_left _ _) (le_of_max_le_left hs)) t _
          (mem_closedBall_zero_iff.2 (hs₂ s (le_trans (le_max_right _ _) (le_of_max_le_left hs)) t))
          i hi
      · have hsT : T ≤ s := le_trans (le_max_left _ _) (le_of_max_le_right hs)
        have hs0 : s₀ < s := by
          have := le_trans (le_max_right _ _) (le_of_max_le_right hs); linarith
        rw [Yg_eq]
        refine (norm_iteratedFDeriv_affine_add_le L3 0 _ (a := s₀)
          (I3.contDiff.comp hgc).contDiffOn hs0 t hi1).trans ?_
        gcongr
        exact (I3.norm_iteratedFDeriv_comp_left (x := (s, t)) hgc.contDiffAt
          (by exact_mod_cast le_top)).trans
          (mul_le_mul_of_nonneg_left (hB i hi s hsT t) (norm_nonneg _)))
  intro m
  obtain ⟨K, s₁, hK⟩ := key m
  exact ⟨K, s₁, fun s hs t => hK () s hs t⟩

/-- **S1, cylinder level.** `C₀(e^{2π(s+it)}) 1 - i` decays. -/
theorem C0_cyl_decay (hρ : 0 < ρ) (hb : 0 < b) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    {r₁ : ℝ} (hr₁ : r₁ < ρ) (hβ : r₁ ≤ β.rIn) (hgr : ∀ x, ‖g x‖ ≤ r₁) (hg : ContDiff ℝ ∞ g)
    {δ : ℝ} (hδ : δ < 0) (hgas : ExpDecayCInfty (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) (-δ)) :
    ∀ d < -δ, ExpDecayCInfty (fun q : ℝ × ℝ => C0 Jbar β g (cylInf q.1 q.2) 1 - Complex.I) d := by
  intro d hd
  have hδ' : 0 < -δ := by linarith
  have hBd := bdH_Fc_Yg hρ hb hT hr₁ hgr hg hδ' hgas
  -- first term
  have hA : ExpDecayCInfty (fun q => ev22 (Fc Jbar (Yg g q)) - Complex.I) d := by
    have hBA : BdH (fun q => ev22 (Fc Jbar (Yg g q)) - Complex.I) :=
      bdH_sub (bdH_clm ev22 hBd) (bdH_const _)
    obtain ⟨CL, sL, hCL⟩ := Fc_lip hρ hb hT
    obtain ⟨s₂, hs₂⟩ := eventually_norm_le hδ' hgas (half_pos hρ)
    obtain ⟨Cg, sg, hCg⟩ := hgas.2 0
    refine expDecay_of_bdH hBA (C := |CL| * Cg) (s₀ := max sL (max s₂ sg)) (fun s hs t => ?_)
      hδ' d hd
    have hsL : sL ≤ s := le_trans (le_max_left _ _) hs
    have hs2 : s₂ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
    have hsg : sg ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
    have hw := hs₂ s hs2 t
    have h1 := hCL s hsL t _ (mem_closedBall_zero_iff.2 hw)
    have h2 := hCg s hsg t
    rw [norm_iteratedFDeriv_zero] at h2
    have hI : Complex.I = ev22 jStd := by simp [ev22, jStd]
    rw [hI, ← map_sub]
    calc ‖ev22 (Fc Jbar (Yg g (s, t)) - jStd)‖
        ≤ ‖ev22‖ * ‖Fc Jbar (Yg g (s, t)) - jStd‖ := le_opNorm _ _
      _ ≤ 1 * (|CL| * ‖g (cylInf s t)‖) := by
          gcongr
          · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            refine mul_le_one₀ (ContinuousLinearMap.norm_snd_le ℝ ℂ ℂ) (norm_nonneg _) ?_
            refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun J => ?_
            simp only [apply_apply, one_mul]
            refine (le_opNorm J _).trans ?_
            have : ‖((0 : ℂ), (1 : ℂ))‖ = 1 := by simp
            rw [this, mul_one]
          · exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
      _ ≤ |CL| * Cg * Real.exp (-(-δ * s)) := by
          rw [one_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  -- second term
  have hB : ExpDecayCInfty (fun q => fderiv ℝ (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) q
      (ev12 (Fc Jbar (Yg g q)))) d :=
    expDecayCInfty_mono (expDecay_bilin (ContinuousLinearMap.apply ℝ ℂ).flip
      (BT.expDecay_fderiv hgas) (bdH_clm ev12 hBd)) hd.le
  have heq : (fun q : ℝ × ℝ => C0 Jbar β g (cylInf q.1 q.2) 1 - Complex.I) =
      fun q => (ev22 (Fc Jbar (Yg g q)) - Complex.I) -
        fderiv ℝ (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) q (ev12 (Fc Jbar (Yg g q))) := by
    funext q
    rw [C0_cyl hβ hgr hg q, ev22_apply, ev12_apply]
    simp only [Fc, Yg]
    ring
  rw [heq]
  exact expDecay_sub hA hB

end

end FiniteEnergyPlane.B3E

/-! B3E layer S1b: decay of `cc ∘ cyl - i`, `Pf ∘ cyl - id` and `qinvL (cc ∘ cyl) - id`. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

lemma qL_contDiffOn : ContDiffOn ℝ ∞ qL {c : ℂ | c.im ≠ 0} := by
  have hW : ContDiffOn ℝ ∞ (fun c : ℂ => (Complex.I - (c.re : ℂ)) * (((c.im)⁻¹ : ℝ) : ℂ))
      {c | c.im ≠ 0} :=
    (contDiffOn_const.sub (Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff).contDiffOn).mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (Complex.imCLM.contDiff.contDiffOn.inv fun c hc => hc))
  have : qL = fun c => Complex.reCLM.smulRight (1 : ℂ) +
      (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM)
        ((Complex.I - (c.re : ℂ)) * (((c.im)⁻¹ : ℝ) : ℂ)) := by
    funext c; rw [qL_eq]; rfl
  rw [this]
  exact contDiffOn_const.add
    ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).contDiff.comp_contDiffOn hW)

lemma qinvL_contDiff' : ContDiff ℝ ∞ qinvL := by
  unfold qinvL
  exact contDiff_const.add ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).contDiff)

lemma qL_I : qL Complex.I = ContinuousLinearMap.id ℝ ℂ :=
  ContinuousLinearMap.ext fun u => by rw [qL_apply]; simp [Complex.re_add_im]

lemma qinvL_I : qinvL Complex.I = ContinuousLinearMap.id ℝ ℂ :=
  ContinuousLinearMap.ext fun u => by rw [qinvL_apply]; simp [Complex.re_add_im]

variable {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
  {Sinf : ℝ → Mat 1} {β : ContDiffBump (0 : ℂ)} {g ψ : ℂ → ℂ}

/-- Standing hypotheses of the asymptotic layers. -/
structure AHyp (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (β : ContDiffBump (0 : ℂ)) (g ψ : ℂ → ℂ) (r₁ δ : ℝ) (κ : ℂ) (b' : ℝ) :
    Prop where
  hρ : 0 < ρ
  hb : 0 < b
  hT : IsStdTubeStructure ρ b Jbar Jinf Sinf
  hr₁ : r₁ < ρ
  hβ : r₁ ≤ β.rIn
  hgr : ∀ x, ‖g x‖ ≤ r₁
  hg : ContDiff ℝ ∞ g
  hδ : δ < 0
  hgas : ExpDecayCInfty (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) (-δ)
  hκ : κ ≠ 0
  hb' : 0 < b'
  hψas : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b'

variable {r₁ δ : ℝ} {κ : ℂ} {b' : ℝ}

theorem AHyp.cc_decay (H : AHyp ρ b Jbar Jinf Sinf β g ψ r₁ δ κ b') :
    ∀ d < -δ, ExpDecayCInfty (fun q : ℝ × ℝ => cc Jbar β g ψ (cylInf q.1 q.2) - Complex.I) d :=
  fun d hd => expDecayCInfty_comp_of_div_sub ψ κ H.hκ b' H.hb' H.hψas
    (fun x => C0 Jbar β g x 1 - Complex.I) d
    (C0_cyl_decay H.hρ H.hb H.hT H.hr₁ H.hβ H.hgr H.hg H.hδ H.hgas d hd)

theorem AHyp.Pf_decay (H : AHyp ρ b Jbar Jinf Sinf β g ψ r₁ δ κ b') {d : ℝ} (hd0 : 0 < d)
    (hd : d < -δ) : ExpDecayCInfty (fun q : ℝ × ℝ =>
      Pf Jbar β g ψ (cylInf q.1 q.2) - ContinuousLinearMap.id ℝ ℂ) d := by
  have hG : ContDiffOn ℝ ∞ (fun a : ℂ => qL (Complex.I + a) - ContinuousLinearMap.id ℝ ℂ)
      (ball (0 : ℂ) (1 / 2)) := by
    refine (qL_contDiffOn.comp (contDiffOn_const.add contDiffOn_id) fun a ha => ?_).sub
      contDiffOn_const
    have h1 := Complex.abs_im_le_norm a
    have h2 := mem_ball_zero_iff.1 ha
    show (Complex.I + id a).im ≠ 0
    rw [id, Complex.add_im, Complex.I_im]
    intro h
    have : a.im = -1 := by linarith
    rw [this] at h1; norm_num at h1; linarith
  have := expDecayCInfty_comp_left _ (1 / 2) (by norm_num) hG (by simp [qL_I]) _ d hd0
    (H.cc_decay d hd)
  refine expDecayCInfty_congr (s₀ := 0) this fun s _ t => ?_
  simp [Pf, add_sub_cancel]

theorem AHyp.qinv_decay (H : AHyp ρ b Jbar Jinf Sinf β g ψ r₁ δ κ b') {d : ℝ} (hd0 : 0 < d)
    (hd : d < -δ) : ExpDecayCInfty (fun q : ℝ × ℝ =>
      qinvL (cc Jbar β g ψ (cylInf q.1 q.2)) - ContinuousLinearMap.id ℝ ℂ) d := by
  have hG : ContDiffOn ℝ ∞ (fun a : ℂ => qinvL (Complex.I + a) - ContinuousLinearMap.id ℝ ℂ)
      (ball (0 : ℂ) (1 / 2)) :=
    ((qinvL_contDiff'.comp (contDiff_const.add contDiff_id)).sub contDiff_const).contDiffOn
  have := expDecayCInfty_comp_left _ (1 / 2) (by norm_num) hG (by simp [qinvL_I]) _ d hd0
    (H.cc_decay d hd)
  refine expDecayCInfty_congr (s₀ := 0) this fun s _ t => ?_
  simp [add_sub_cancel]

end

end FiniteEnergyPlane.B3E

/-! B3E layer F: bounded-derivative calculus for families `f θ`, uniformly in `θ`. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Real Nat

noncomputable section

variable {ι E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A family smooth on a common half-plane, with derivative bounds uniform in the parameter. -/
def BdF (f : ι → ℝ × ℝ → F) : Prop :=
  (∃ s₀ : ℝ, ∀ θ, ContDiffOn ℝ ∞ (f θ) (Ioi s₀ ×ˢ univ)) ∧
    ∀ m : ℕ, ∃ C s₁ : ℝ, ∀ θ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m (f θ) (s, t)‖ ≤ C

lemma BdF.upTo {f : ι → ℝ × ℝ → F} (hf : BdF f) (k : ℕ) :
    ∃ B T : ℝ, 0 ≤ B ∧ ∀ i ≤ k, ∀ θ, ∀ s ≥ T, ∀ t : ℝ, ‖iteratedFDeriv ℝ i (f θ) (s, t)‖ ≤ B := by
  choose Ci si hCi using hf.2
  refine ⟨∑ i ∈ Finset.range (k + 1), |Ci i|, ∑ i ∈ Finset.range (k + 1), |si i|,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, fun i hi θ s hs t => ?_⟩
  have hmem : i ∈ Finset.range (k + 1) := Finset.mem_range.2 (by omega)
  have hsi : si i ≤ s := (le_abs_self _).trans ((Finset.single_le_sum (f := fun i => |si i|)
    (fun _ _ => abs_nonneg _) hmem).trans hs)
  exact (hCi i θ s hsi t).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |Ci i|) (fun _ _ => abs_nonneg _) hmem))

lemma bdF_of_bdH {f : ℝ × ℝ → F} (hf : BdH f) : BdF (fun _ : ι => f) := by
  obtain ⟨⟨s₀, h0⟩, hb⟩ := hf
  exact ⟨⟨s₀, fun _ => h0⟩, fun m => by obtain ⟨C, s₁, h⟩ := hb m; exact ⟨C, s₁, fun _ => h⟩⟩

lemma BdF.bdH {f : ι → ℝ × ℝ → F} (hf : BdF f) (θ : ι) : BdH (f θ) := by
  obtain ⟨⟨s₀, h0⟩, hb⟩ := hf
  exact ⟨⟨s₀, h0 θ⟩, fun m => by obtain ⟨C, s₁, h⟩ := hb m; exact ⟨C, s₁, h θ⟩⟩

lemma bdF_add {f g : ι → ℝ × ℝ → F} (hf : BdF f) (hg : BdF g) :
    BdF (fun θ p => f θ p + g θ p) := by
  obtain ⟨⟨s₁, hf1⟩, hbf⟩ := hf
  obtain ⟨⟨s₂, hg1⟩, hbg⟩ := hg
  refine ⟨⟨max s₁ s₂, fun θ => ((hf1 θ).mono (hp_mono (le_max_left _ _))).add
    ((hg1 θ).mono (hp_mono (le_max_right _ _)))⟩, fun m => ?_⟩
  obtain ⟨C₁, a₁, h₁⟩ := hbf m
  obtain ⟨C₂, a₂, h₂⟩ := hbg m
  refine ⟨C₁ + C₂, max (max a₁ a₂) (max s₁ s₂ + 1), fun θ s hs t => ?_⟩
  have ha := le_of_max_le_left hs
  have hs' : max s₁ s₂ < s := by linarith [le_of_max_le_right hs]
  beta_reduce
  rw [show (fun p => f θ p + g θ p) = f θ + g θ from rfl,
    iteratedFDeriv_add_apply (contDiffAt_hp (hf1 θ) (lt_of_le_of_lt (le_max_left _ _) hs') t m)
      (contDiffAt_hp (hg1 θ) (lt_of_le_of_lt (le_max_right _ _) hs') t m)]
  exact (norm_add_le _ _).trans (add_le_add (h₁ θ s (le_of_max_le_left ha) t)
    (h₂ θ s (le_of_max_le_right ha) t))

lemma bdF_bilin (B : F →L[ℝ] G →L[ℝ] H) {f : ι → ℝ × ℝ → F} {g : ι → ℝ × ℝ → G}
    (hf : BdF f) (hg : BdF g) : BdF (fun θ p => B (f θ p) (g θ p)) := by
  obtain ⟨⟨s₁, hf1⟩, hbf⟩ := hf
  obtain ⟨⟨s₂, hg1⟩, hbg⟩ := hg
  set s₀ := max s₁ s₂
  have hf0 := fun θ => (hf1 θ).mono (hp_mono (le_max_left s₁ s₂))
  have hg0 := fun θ => (hg1 θ).mono (hp_mono (le_max_right s₁ s₂))
  refine ⟨⟨s₀, fun θ => (B.contDiff.comp_contDiffOn (hf0 θ)).clm_apply (hg0 θ)⟩, fun m => ?_⟩
  obtain ⟨B₁, T₁, hB₁, h₁⟩ := (show BdF f from ⟨⟨s₁, hf1⟩, hbf⟩).upTo m
  obtain ⟨B₂, T₂, hB₂, h₂⟩ := (show BdF g from ⟨⟨s₂, hg1⟩, hbg⟩).upTo m
  refine ⟨‖B‖ * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B₁ * B₂,
    max (max T₁ T₂) (s₀ + 1), fun θ s hs t => ?_⟩
  have hT := le_of_max_le_left hs
  have hs0 : s₀ < s := by linarith [le_of_max_le_right hs]
  refine (norm_bilin_hp B (hf0 θ) (hg0 θ) hs0 t m).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by positivity)
  have e1 := h₁ i (by simpa [Nat.lt_succ_iff] using hi) θ s (le_of_max_le_left hT) t
  have e2 := h₂ (m - i) (Nat.sub_le _ _) θ s (le_of_max_le_right hT) t
  exact mul_le_mul (mul_le_mul_of_nonneg_left e1 (Nat.cast_nonneg _)) e2 (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hB₁)

lemma bdF_clm (L : F →L[ℝ] G) {f : ι → ℝ × ℝ → F} (hf : BdF f) :
    BdF (fun θ p => L (f θ p)) := by
  obtain ⟨⟨s₁, hf1⟩, hbf⟩ := hf
  refine ⟨⟨s₁, fun θ => L.contDiff.comp_contDiffOn (hf1 θ)⟩, fun m => ?_⟩
  obtain ⟨C, a, h⟩ := hbf m
  refine ⟨‖L‖ * C, max a (s₁ + 1), fun θ s hs t => ?_⟩
  have hs1 : s₁ < s := by linarith [le_of_max_le_right hs]
  beta_reduce
  rw [show (fun p => L (f θ p)) = L ∘ f θ from rfl,
    L.iteratedFDeriv_comp_left (contDiffAt_hp (hf1 θ) hs1 t m) le_rfl]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_left (h θ s (le_of_max_le_left hs) t) (norm_nonneg _))

/-- Composition with a fixed smooth map, bounded along the family, with inner maps whose
derivatives of order `≥ 1` are bounded. -/
lemma bdF_comp (Φ : E → F) (V : Set E) (hV : IsOpen V) (hΦ : ContDiffOn ℝ ∞ Φ V)
    (X : ι → ℝ × ℝ → E) (a : ℝ) (hX : ∀ θ, ContDiffOn ℝ ∞ (X θ) (Ioi a ×ˢ univ))
    (hXV : ∀ θ, ∀ s > a, ∀ t, X θ (s, t) ∈ V)
    (hb : ∀ n : ℕ, ∃ C D s₁ : ℝ, ∀ θ, ∀ s ≥ s₁, ∀ t,
      (∀ i ≤ n, ‖iteratedFDeriv ℝ i Φ (X θ (s, t))‖ ≤ C) ∧
      ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (X θ) (s, t)‖ ≤ D) :
    BdF (fun θ p => Φ (X θ p)) :=
  ⟨⟨a, fun θ => hΦ.comp (hX θ) fun q hq => hXV θ q.1 hq.1 q.2⟩,
    bd_comp_hp Φ V hV hΦ X a hX hXV hb⟩

/-- `BdH` of a parameter integral over `[0, 1]` of a jointly smooth integrand, from bounds of the
integrand (along `θ ∈ [0, 1]`) far out. -/
lemma bdH_integral [CompleteSpace F] (P : ℝ × ℝ → ℝ → F)
    (hP : ContDiff ℝ ∞ (Function.uncurry P))
    (hb : ∀ m : ℕ, ∃ C s₁ : ℝ, ∀ θ ∈ Icc (0 : ℝ) 1, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p => P p θ) (s, t)‖ ≤ C) :
    BdH (fun p => ∫ θ in (0 : ℝ)..1, P p θ) :=
  ⟨⟨0, (ContWeatherall.contDiff_parametric_intervalIntegral hP 0 1).contDiffOn⟩,
    bd_integral P hP hb⟩

end

end FiniteEnergyPlane.B3E

/-! B3E layer K: the `a`-derivatives of `Afun`, `Bfun` in cylindrical coordinates. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

/-- `Ablk · G` as a continuous linear map. -/
def AblkL (G : ℂ →L[ℝ] ℂ) : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun J => Ablk J G
      map_add' := fun J J' => by
        ext1 x; simp [Ablk, J11, J12, J21, J22]; abel
      map_smul' := fun c J => by
        ext1 x; simp [Ablk, J11, J12, J21, J22, smul_sub, smul_add] }

@[simp] lemma AblkL_apply (G : ℂ →L[ℝ] ℂ) (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) : AblkL G J = Ablk J G := rfl

/-- `Bblk · G` as a continuous linear map. -/
def BblkL (G : ℂ →L[ℝ] ℂ) : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun J => Bblk J G
      map_add' := fun J J' => by
        ext1 x; simp [Bblk, J12, J22]; abel
      map_smul' := fun c J => by
        ext1 x; simp [Bblk, J12, J22, smul_sub] }

@[simp] lemma BblkL_apply (G : ℂ →L[ℝ] ℂ) (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) : BblkL G J = Bblk J G := rfl

/-- Conjugation by the cylindrical scaling. -/
def conjL (s t : ℝ) : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ) :=
  (compL ℝ (ℂ × ℂ) (ℂ × ℂ) (ℂ × ℂ) (cylScale s t)).comp
    ((compL ℝ (ℂ × ℂ) (ℂ × ℂ) (ℂ × ℂ)).flip (cylScaleInv s t))

lemma conjL_apply (s t : ℝ) (M : ℂ × ℂ →L[ℝ] ℂ × ℂ) (v : ℂ × ℂ) :
    conjL s t M v = cylScale s t (M (cylScaleInv s t v)) := rfl

lemma Jbar_eq_conjL (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (s t : ℝ) (w : ℂ) :
    Jbar (cylInf s t, w) = conjL s t (cylJ Jbar s t w) :=
  ContinuousLinearMap.ext fun v => by rw [conjL_apply, Jbar_cyl]

section conj
variable (s t : ℝ) (M : ℂ × ℂ →L[ℝ] ℂ × ℂ)

lemma J11_conj (u : ℂ) : J11 (conjL s t M) u = lam s t * J11 M ((lam s t)⁻¹ * u) := by
  simp [J11, conjL_apply, cylScale_apply, cylScaleInv_apply]

lemma J12_conj (u : ℂ) : J12 (conjL s t M) u = lam s t * J12 M u := by
  simp [J12, conjL_apply, cylScale_apply, cylScaleInv_apply]

lemma J21_conj (u : ℂ) : J21 (conjL s t M) u = J21 M ((lam s t)⁻¹ * u) := by
  simp [J21, conjL_apply, cylScale_apply, cylScaleInv_apply]

lemma J22_conj (u : ℂ) : J22 (conjL s t M) u = J22 M u := by
  simp [J22, conjL_apply, cylScale_apply, cylScaleInv_apply]

lemma Ablk_conj (G : ℂ →L[ℝ] ℂ) (u : ℂ) :
    Ablk (conjL s t M) G u = Ablk M (G.comp (mulL (lam s t))) ((lam s t)⁻¹ * u) := by
  have hl : lam s t * ((lam s t)⁻¹ * u) = u := by
    rw [← mul_assoc, mul_inv_cancel₀ (lam_ne s t), one_mul]
  simp only [Ablk, sub_apply, add_apply, comp_apply, J11_conj, J12_conj, J21_conj, J22_conj,
    mulL_apply, hl]

lemma Bblk_conj (G : ℂ →L[ℝ] ℂ) (u : ℂ) :
    Bblk (conjL s t M) G u = Bblk M (G.comp (mulL (lam s t))) u := by
  simp only [Bblk, sub_apply, comp_apply, J12_conj, J22_conj, mulL_apply]

end conj

/-- The `w`-derivative of `cylJ`. -/
def DwF (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (r : ℝ × ℝ × ℂ) :
    ℂ →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ) := (fderiv ℝ (Fc Jbar) r).comp I3

/-- `Ĝ(σ, τ) = Dĝ(σ, τ) ∘ (re, im)`. -/
def Ghat (g : ℂ → ℂ) (q : ℝ × ℝ) : ℂ →L[ℝ] ℂ :=
  (fderiv ℝ (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) q).comp cToR

lemma Ghat_eq {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (q : ℝ × ℝ) :
    (fderiv ℝ g (cylInf q.1 q.2)).comp (mulL (lam q.1 q.2)) = Ghat g q :=
  ContinuousLinearMap.ext fun u => by
    simp only [Ghat, comp_apply, mulL_apply, fderiv_gc_apply hg]

variable {ρ : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {β : ContDiffBump (0 : ℂ)} {g : ℂ → ℂ}

/-- Near a point where the retraction is the identity, `Afun`/`Bfun` at `cylInf σ τ` are linear
images of `cylJ`. -/
lemma Afun_Bfun_eventually {σ τ : ℝ} {a₀ : ℂ}
    (ha : ‖g (cylInf σ τ) + a₀‖ < β.rIn) :
    (fun a => Afun Jbar β g (cylInf σ τ, a)) =ᶠ[𝓝 a₀]
        (fun a => AblkL (fderiv ℝ g (cylInf σ τ))
          (conjL σ τ (Fc Jbar (σ, τ, g (cylInf σ τ) + a)))) ∧
      (fun a => Bfun Jbar β g (cylInf σ τ, a)) =ᶠ[𝓝 a₀]
        (fun a => BblkL (fderiv ℝ g (cylInf σ τ))
          (conjL σ τ (Fc Jbar (σ, τ, g (cylInf σ τ) + a)))) := by
  have hO : IsOpen {a : ℂ | ‖g (cylInf σ τ) + a‖ < β.rIn} :=
    isOpen_lt (continuous_const.add continuous_id).norm continuous_const
  have hmem : {a : ℂ | ‖g (cylInf σ τ) + a‖ < β.rIn} ∈ 𝓝 a₀ := hO.mem_nhds ha
  have key : ∀ a ∈ {a : ℂ | ‖g (cylInf σ τ) + a‖ < β.rIn},
      Jt Jbar β (cylInf σ τ, g (cylInf σ τ) + a) =
        conjL σ τ (Fc Jbar (σ, τ, g (cylInf σ τ) + a)) := by
    intro a ha
    simp only [Jt, rtr_eq β (le_of_lt ha), Fc]
    exact Jbar_eq_conjL Jbar σ τ _
  refine ⟨Filter.eventuallyEq_of_mem hmem fun a ha => ?_,
    Filter.eventuallyEq_of_mem hmem fun a ha => ?_⟩
  · simp only [Afun, AblkL_apply, key a ha]
  · simp only [Bfun, BblkL_apply, key a ha]

lemma hasFDerivAt_Fc_shift {s₀ : ℝ} (hFc : ContDiffOn ℝ ∞ (Fc Jbar) (Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ))
    {σ τ : ℝ} (hσ : s₀ < σ) {w₀ a₀ : ℂ} (hw : ‖w₀ + a₀‖ < ρ) :
    HasFDerivAt (fun a => Fc Jbar (σ, τ, w₀ + a)) (DwF Jbar (σ, τ, w₀ + a₀)) a₀ := by
  have hO : IsOpen (Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ) :=
    isOpen_Ioi.prod ((isOpen_univ (X := ℝ)).prod (isOpen_ball (x := (0 : ℂ))))
  have hd : HasFDerivAt (Fc Jbar) (fderiv ℝ (Fc Jbar) (σ, τ, w₀ + a₀)) (σ, τ, w₀ + a₀) :=
    ((hFc.contDiffAt (hO.mem_nhds (show ((σ, τ, w₀ + a₀) : ℝ × ℝ × ℂ) ∈
      Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ from
        ⟨hσ, mem_univ _, mem_ball_zero_iff.2 hw⟩))).differentiableAt (by simp)).hasFDerivAt
  have hin : HasFDerivAt (fun a : ℂ => ((σ, τ, w₀ + a) : ℝ × ℝ × ℂ)) I3 a₀ := by
    have h1 := I3.hasFDerivAt.const_add ((σ, τ, w₀) : ℝ × ℝ × ℂ) (x := a₀)
    have e : (fun a : ℂ => ((σ, τ, w₀) : ℝ × ℝ × ℂ) + I3 a) =
        fun a : ℂ => ((σ, τ, w₀ + a) : ℝ × ℝ × ℂ) := by
      funext a; simp [I3]
    rwa [e] at h1
  exact hd.comp a₀ hin

/-- The cylindrical form of the `a`-derivatives of `Afun`, `Bfun`. -/
theorem fderiv_Afun_Bfun_cyl {s₀ : ℝ}
    (hFc : ContDiffOn ℝ ∞ (Fc Jbar) (Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ)) (hg : ContDiff ℝ ∞ g)
    (hβρ : β.rIn ≤ ρ) {σ τ : ℝ} (hσ : s₀ < σ) {a₀ : ℂ}
    (ha : ‖g (cylInf σ τ) + a₀‖ < β.rIn) (u y : ℂ) :
    fderiv ℝ (fun a => Afun Jbar β g (cylInf σ τ, a)) a₀ u y =
        Ablk (DwF Jbar (σ, τ, g (cylInf σ τ) + a₀) u) (Ghat g (σ, τ)) ((lam σ τ)⁻¹ * y) ∧
      fderiv ℝ (fun a => Bfun Jbar β g (cylInf σ τ, a)) a₀ u y =
        Bblk (DwF Jbar (σ, τ, g (cylInf σ τ) + a₀) u) (Ghat g (σ, τ)) y := by
  obtain ⟨hA, hB⟩ := Afun_Bfun_eventually (Jbar := Jbar) ha
  have hF := hasFDerivAt_Fc_shift hFc hσ (lt_of_lt_of_le ha hβρ) (τ := τ)
  have hA' : HasFDerivAt (fun a => AblkL (fderiv ℝ g (cylInf σ τ))
      (conjL σ τ (Fc Jbar (σ, τ, g (cylInf σ τ) + a))))
      (((AblkL (fderiv ℝ g (cylInf σ τ))).comp (conjL σ τ)).comp
        (DwF Jbar (σ, τ, g (cylInf σ τ) + a₀))) a₀ :=
    ((AblkL (fderiv ℝ g (cylInf σ τ))).comp (conjL σ τ)).hasFDerivAt.comp a₀ hF
  have hB' : HasFDerivAt (fun a => BblkL (fderiv ℝ g (cylInf σ τ))
      (conjL σ τ (Fc Jbar (σ, τ, g (cylInf σ τ) + a))))
      (((BblkL (fderiv ℝ g (cylInf σ τ))).comp (conjL σ τ)).comp
        (DwF Jbar (σ, τ, g (cylInf σ τ) + a₀))) a₀ :=
    ((BblkL (fderiv ℝ g (cylInf σ τ))).comp (conjL σ τ)).hasFDerivAt.comp a₀ hF
  have hq : (fderiv ℝ g (cylInf σ τ)).comp (mulL (lam σ τ)) = Ghat g (σ, τ) := Ghat_eq hg (σ, τ)
  refine ⟨?_, ?_⟩
  · rw [hA.fderiv_eq, hA'.fderiv]
    simp only [comp_apply, AblkL_apply, Ablk_conj, hq]
  · rw [hB.fderiv_eq, hB'.fderiv]
    simp only [comp_apply, BblkL_apply, Bblk_conj, hq]

end

end FiniteEnergyPlane.B3E

/-! B3E layer S2: log coordinates of `ψ` and the decaying building blocks. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

/-- `(a, b) ↦ a + b i`. -/
def cplx : ℝ × ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (1 : ℂ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I

lemma cplx_apply (v : ℝ × ℝ) : cplx v = v.1 + v.2 * Complex.I := by simp [cplx, mul_comm]

lemma cyl_fderiv_apply (p v : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => cylInf q.1 q.2) p v = lam p.1 p.2 * cplx v := by
  obtain ⟨L, hL, hL1, hL2⟩ := cyl_hasFDerivAt p
  rw [hL.fderiv]
  have e : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [e]
  rw [map_add, map_smul, map_smul, hL1, hL2, cplx_apply]
  simp only [lam, Complex.real_smul]
  ring

/-- Chain rule through the cylindrical coordinates. -/
lemma fderiv_comp_cyl_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F}
    (hf : ContDiff ℝ ∞ f) (q v : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => f (cylInf p.1 p.2)) q v =
      fderiv ℝ f (cylInf q.1 q.2) (lam q.1 q.2 * cplx v) := by
  have hc : DifferentiableAt ℝ (fun p : ℝ × ℝ => cylInf p.1 p.2) q :=
    (cyl_contDiff.differentiable (by simp)) q
  have hfd := (hf.differentiable (by simp)) (cylInf q.1 q.2)
  have : HasFDerivAt (fun p : ℝ × ℝ => f (cylInf p.1 p.2))
      ((fderiv ℝ f (cylInf q.1 q.2)).comp (fderiv ℝ (fun p : ℝ × ℝ => cylInf p.1 p.2) q)) q :=
    hfd.hasFDerivAt.comp q hc.hasFDerivAt
  rw [this.fderiv, comp_apply, cyl_fderiv_apply]

/-- The constant shift of the log coordinates. -/
def cshift (κ : ℂ) : ℝ × ℝ := (Real.log ‖κ‖ / (2 * π), Complex.arg κ / (2 * π))

/-- Log coordinates. -/
def Psi (κ : ℂ) (E : ℝ × ℝ → ℝ × ℝ) (q : ℝ × ℝ) : ℝ × ℝ := q + cshift κ + E q

/-- Log-coordinate data for `ψ`. -/
structure LCData (ψ : ℂ → ℂ) (κ : ℂ) (b' : ℝ) (E : ℝ × ℝ → ℝ × ℝ) (S : ℝ) : Prop where
  hE : ExpDecayCInfty E b'
  heq : ∀ s ≥ S, ∀ t : ℝ, ψ (cylInf s t) = cylInf (Psi κ E (s, t)).1 (Psi κ E (s, t)).2

variable {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
  {Sinf : ℝ → Mat 1} {β : ContDiffBump (0 : ℂ)} {g ψ v : ℂ → ℂ} {r₁ δ : ℝ} {κ : ℂ} {b' : ℝ}

lemma AHyp.exists_LCData (H : AHyp ρ b Jbar Jinf Sinf β g ψ r₁ δ κ b') :
    ∃ E S, LCData ψ κ b' E S := by
  obtain ⟨E, S, hE, h⟩ := exists_logCoords_of_div_sub ψ κ H.hκ b' H.hb' H.hψas
  exact ⟨E, S, hE, h⟩

/-- `ĝ ∘ Ψ` decays. -/
lemma gPsi_decay (H : AHyp ρ b Jbar Jinf Sinf β g ψ r₁ δ κ b') {E : ℝ × ℝ → ℝ × ℝ} {S : ℝ}
    (hL : LCData ψ κ b' E S) :
    ExpDecayCInfty (fun q => g (cylInf (Psi κ E q).1 (Psi κ E q).2)) (-δ) :=
  expDecayCInfty_comp_shift (fun p => g (cylInf p.1 p.2)) (-δ) H.hgas E b' H.hb' hL.hE (cshift κ)

lemma Ghat_decay (H : AHyp ρ b Jbar Jinf Sinf β g ψ r₁ δ κ b') :
    ExpDecayCInfty (Ghat g) (-δ) :=
  expDecay_clm ((compL ℝ ℂ (ℝ × ℝ) ℂ).flip cToR) (BT.expDecay_fderiv H.hgas)

lemma GPsi_decay (H : AHyp ρ b Jbar Jinf Sinf β g ψ r₁ δ κ b') {E : ℝ × ℝ → ℝ × ℝ} {S : ℝ}
    (hL : LCData ψ κ b' E S) : ExpDecayCInfty (fun q => Ghat g (Psi κ E q)) (-δ) :=
  expDecayCInfty_comp_shift (Ghat g) (-δ) (Ghat_decay H) E b' H.hb' hL.hE (cshift κ)

/-- `ĥ = hd ∘ cyl` decays. -/
lemma hd_decay (H : AHyp ρ b Jbar Jinf Sinf β g ψ r₁ δ κ b')
    (hvas : ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ)) :
    ExpDecayCInfty (fun q : ℝ × ℝ => hd g ψ v (cylInf q.1 q.2)) (-δ) :=
  expDecay_sub hvas (expDecayCInfty_comp_of_div_sub ψ κ H.hκ b' H.hb' H.hψas g (-δ) H.hgas)

/-- `∂ₛ ĥ` decays and equals `Dhd(z)(2πz)`. -/
lemma dhd_decay (H : AHyp ρ b Jbar Jinf Sinf β g ψ r₁ δ κ b')
    (hvas : ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ)) :
    ExpDecayCInfty (fun q : ℝ × ℝ =>
      fderiv ℝ (fun p : ℝ × ℝ => hd g ψ v (cylInf p.1 p.2)) q ((1 : ℝ), (0 : ℝ))) (-δ) :=
  expDecay_clm (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : ℝ)))
    (BT.expDecay_fderiv (hd_decay H hvas))

lemma dhd_eq (hhd : ContDiff ℝ ∞ (hd g ψ v)) (q : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => hd g ψ v (cylInf p.1 p.2)) q ((1 : ℝ), (0 : ℝ)) =
      fderiv ℝ (hd g ψ v) (cylInf q.1 q.2) (lam q.1 q.2) := by
  rw [fderiv_comp_cyl_apply hhd, cplx_apply]; simp

/-- The partial derivatives of `Pf ∘ cyl` decay. -/
lemma dPf_decay (H : AHyp ρ b Jbar Jinf Sinf β g ψ r₁ δ κ b') {d : ℝ} (hd0 : 0 < d)
    (hd : d < -δ) (v₀ : ℝ × ℝ) :
    ExpDecayCInfty (fun q : ℝ × ℝ =>
      fderiv ℝ (fun p : ℝ × ℝ => Pf Jbar β g ψ (cylInf p.1 p.2)) q v₀) d := by
  have h1 := BT.expDecay_fderiv (H.Pf_decay hd0 hd)
  have h2 : (fderiv ℝ fun q : ℝ × ℝ =>
      Pf Jbar β g ψ (cylInf q.1 q.2) - ContinuousLinearMap.id ℝ ℂ) =
      fderiv ℝ (fun p : ℝ × ℝ => Pf Jbar β g ψ (cylInf p.1 p.2)) := by
    funext q; exact fderiv_sub_const _
  rw [h2] at h1
  exact expDecay_clm (ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] ℂ) v₀) h1

lemma dPf_eq (hP : ContDiff ℝ ∞ (Pf Jbar β g ψ)) (q : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => Pf Jbar β g ψ (cylInf p.1 p.2)) q ((1 : ℝ), (0 : ℝ)) =
        fderiv ℝ (Pf Jbar β g ψ) (cylInf q.1 q.2) (lam q.1 q.2) ∧
      fderiv ℝ (fun p : ℝ × ℝ => Pf Jbar β g ψ (cylInf p.1 p.2)) q ((0 : ℝ), (1 : ℝ)) =
        fderiv ℝ (Pf Jbar β g ψ) (cylInf q.1 q.2) (Complex.I * lam q.1 q.2) := by
  refine ⟨?_, ?_⟩ <;> rw [fderiv_comp_cyl_apply hP, cplx_apply] <;> simp [mul_comm]

/-- The ratio `R = 1 + (∂ₛE₁ + i ∂ₛE₂)`. -/
def Rr (E : ℝ × ℝ → ℝ × ℝ) (q : ℝ × ℝ) : ℂ := 1 + cplx (fderiv ℝ E q ((1 : ℝ), (0 : ℝ)))

lemma Rr_decay {E : ℝ × ℝ → ℝ × ℝ} (hE : ExpDecayCInfty E b') :
    ExpDecayCInfty (fun q => Rr E q - 1) b' := by
  have := expDecay_clm (cplx.comp (ContinuousLinearMap.apply ℝ (ℝ × ℝ) ((1 : ℝ), (0 : ℝ))))
    (BT.expDecay_fderiv hE)
  refine expDecayCInfty_congr (s₀ := 0) this fun s _ t => ?_
  simp [Rr]

/-- `λ(Ψ)⁻¹ Dψ(z)(λ) = R` far out. -/
lemma Rr_eq (hψ : ContDiff ℝ ∞ ψ) {E : ℝ × ℝ → ℝ × ℝ} {S : ℝ} (hL : LCData ψ κ b' E S) :
    ∃ S' : ℝ, ∀ s > S', ∀ t : ℝ,
      (lam (Psi κ E (s, t)).1 (Psi κ E (s, t)).2)⁻¹ *
        fderiv ℝ ψ (cylInf s t) (lam s t) = Rr E (s, t) := by
  obtain ⟨⟨s₀, hE0⟩, -⟩ := hL.hE
  refine ⟨max S s₀, fun s hs t => ?_⟩
  have hsS : S < s := lt_of_le_of_lt (le_max_left _ _) hs
  have hs0 : s₀ < s := lt_of_le_of_lt (le_max_right _ _) hs
  have hEd : DifferentiableAt ℝ E (s, t) :=
    ((hE0.contDiffAt ((hp_open s₀).mem_nhds (show ((s, t) : ℝ × ℝ) ∈ Ioi s₀ ×ˢ univ from
      ⟨hs0, mem_univ t⟩))).differentiableAt (by simp))
  have hO : IsOpen (Ioi S ×ˢ (univ : Set ℝ)) := hp_open S
  have heqn : (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2)) =ᶠ[𝓝 (s, t)]
      (fun p : ℝ × ℝ => cylInf (Psi κ E p).1 (Psi κ E p).2) :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds (show ((s, t) : ℝ × ℝ) ∈ Ioi S ×ˢ univ from
      ⟨hsS, mem_univ t⟩)) fun p hp => hL.heq p.1 (le_of_lt hp.1) p.2
  have hPsi : HasFDerivAt (Psi κ E) (ContinuousLinearMap.id ℝ (ℝ × ℝ) + fderiv ℝ E (s, t))
      (s, t) := by
    have := ((hasFDerivAt_id (s, t)).add_const (cshift κ)).add hEd.hasFDerivAt
    exact this
  have hc : DifferentiableAt ℝ (fun p : ℝ × ℝ => cylInf p.1 p.2) (Psi κ E (s, t)) :=
    (cyl_contDiff.differentiable (by simp)) _
  have hcomp : HasFDerivAt (fun p : ℝ × ℝ => cylInf (Psi κ E p).1 (Psi κ E p).2)
      ((fderiv ℝ (fun p : ℝ × ℝ => cylInf p.1 p.2) (Psi κ E (s, t))).comp
        (ContinuousLinearMap.id ℝ (ℝ × ℝ) + fderiv ℝ E (s, t))) (s, t) :=
    hc.hasFDerivAt.comp (s, t) hPsi
  have key := congrArg (fun L : ℝ × ℝ →L[ℝ] ℂ => L ((1 : ℝ), (0 : ℝ)))
    (heqn.fderiv_eq.trans hcomp.fderiv)
  rw [fderiv_comp_cyl_apply hψ, comp_apply, add_apply, id_apply, cyl_fderiv_apply,
    cplx_apply, map_add, cplx_apply] at key
  simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero, mul_one] at key
  rw [key, Rr, cplx_apply, ← mul_assoc, inv_mul_cancel₀ (lam_ne _ _), one_mul]

end

end FiniteEnergyPlane.B3E

/-! B3E layer S3a: family tools and the polynomial maps `ΦA`, `ΦB`. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

variable {ι E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma bdF_const_family (c : ι → F) (K : ℝ) (hc : ∀ θ, ‖c θ‖ ≤ K) :
    BdF (fun θ (_ : ℝ × ℝ) => c θ) := by
  refine ⟨⟨0, fun θ => contDiffOn_const⟩, fun m => ⟨|K|, 0, fun θ s _ t => ?_⟩⟩
  rcases m with _ | m
  · simpa using (hc θ).trans (le_abs_self K)
  · rw [iteratedFDeriv_const_of_ne (by omega)]; simp

lemma bdF_prod {f : ι → ℝ × ℝ → F} {g : ι → ℝ × ℝ → G} (hf : BdF f) (hg : BdF g) :
    BdF (fun θ p => (f θ p, g θ p)) := by
  have := bdF_add (bdF_clm (ContinuousLinearMap.inl ℝ F G) hf)
    (bdF_clm (ContinuousLinearMap.inr ℝ F G) hg)
  simpa using this

/-- A globally smooth map of a bounded family is bounded. -/
lemma bdF_comp_smooth [FiniteDimensional ℝ E] (Φ : E → F) (hΦ : ContDiff ℝ ∞ Φ)
    {X : ι → ℝ × ℝ → E} (hX : BdF X) : BdF (fun θ p => Φ (X θ p)) := by
  obtain ⟨B₀, T₀, hB₀, h0⟩ := hX.upTo 0
  obtain ⟨a, hXs⟩ := hX.1
  refine bdF_comp Φ univ isOpen_univ hΦ.contDiffOn X a hXs (fun _ _ _ _ => mem_univ _)
    fun n => ?_
  have hK : IsCompact (closedBall (0 : E) B₀) := isCompact_closedBall _ _
  choose C hC using fun i : ℕ => hK.exists_bound_of_continuousOn
    ((hΦ.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).continuousOn)
  obtain ⟨D, T, -, hD⟩ := hX.upTo n
  refine ⟨∑ i ∈ Finset.range (n + 1), |C i|, D, max T₀ T, fun θ s hs t =>
    ⟨fun i hi => ?_, fun i _ hi => hD i hi θ s (le_of_max_le_right hs) t⟩⟩
  have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have hx : X θ (s, t) ∈ closedBall (0 : E) B₀ := by
    have := h0 0 le_rfl θ s (le_of_max_le_left hs) t
    rw [norm_iteratedFDeriv_zero] at this
    exact mem_closedBall_zero_iff.2 this
  exact (hC i _ hx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) hmem))

/-! ### Block maps as linear maps -/

def J11L : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  (compL ℝ ℂ (ℂ × ℂ) ℂ (fst ℝ ℂ ℂ)).comp ((compL ℝ ℂ (ℂ × ℂ) (ℂ × ℂ)).flip (inl ℝ ℂ ℂ))
def J12L : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  (compL ℝ ℂ (ℂ × ℂ) ℂ (fst ℝ ℂ ℂ)).comp ((compL ℝ ℂ (ℂ × ℂ) (ℂ × ℂ)).flip (inr ℝ ℂ ℂ))
def J21L : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  (compL ℝ ℂ (ℂ × ℂ) ℂ (snd ℝ ℂ ℂ)).comp ((compL ℝ ℂ (ℂ × ℂ) (ℂ × ℂ)).flip (inl ℝ ℂ ℂ))
def J22L : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  (compL ℝ ℂ (ℂ × ℂ) ℂ (snd ℝ ℂ ℂ)).comp ((compL ℝ ℂ (ℂ × ℂ) (ℂ × ℂ)).flip (inr ℝ ℂ ℂ))

@[simp] lemma J11L_apply (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) : J11L J = J11 J := rfl
@[simp] lemma J12L_apply (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) : J12L J = J12 J := rfl
@[simp] lemma J21L_apply (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) : J21L J = J21 J := rfl
@[simp] lemma J22L_apply (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) : J22L J = J22 J := rfl

abbrev DSp := ℂ →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ)

/-- `(D, G, y) ↦ (u ↦ Ablk (D u) G y)`. -/
def PhiA (x : DSp × (ℂ →L[ℝ] ℂ) × ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.apply ℝ ℂ x.2.2).comp (J21L.comp x.1) -
    x.2.1.comp ((ContinuousLinearMap.apply ℝ ℂ x.2.2).comp (J11L.comp x.1)) +
    (ContinuousLinearMap.apply ℝ ℂ (x.2.1 x.2.2)).comp (J22L.comp x.1) -
    x.2.1.comp ((ContinuousLinearMap.apply ℝ ℂ (x.2.1 x.2.2)).comp (J12L.comp x.1))

lemma PhiA_apply (x : DSp × (ℂ →L[ℝ] ℂ) × ℂ) (u : ℂ) :
    PhiA x u = Ablk (x.1 u) x.2.1 x.2.2 := by
  simp [PhiA, Ablk]

/-- `(D, G) ↦ (u ↦ Bblk (D u) G)`. -/
def PhiB (x : DSp × (ℂ →L[ℝ] ℂ)) : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  J22L.comp x.1 - (compL ℝ ℂ ℂ ℂ x.2).comp (J12L.comp x.1)

lemma PhiB_apply (x : DSp × (ℂ →L[ℝ] ℂ)) (u : ℂ) : PhiB x u = Bblk (x.1 u) x.2 := by
  ext1 y; simp [PhiB, Bblk]

lemma PhiA_contDiff : ContDiff ℝ ∞ PhiA := by
  have hD : ContDiff ℝ ∞ (fun x : DSp × (ℂ →L[ℝ] ℂ) × ℂ => x.1) := contDiff_fst
  have hG : ContDiff ℝ ∞ (fun x : DSp × (ℂ →L[ℝ] ℂ) × ℂ => x.2.1) := contDiff_snd.fst
  have hy : ContDiff ℝ ∞ (fun x : DSp × (ℂ →L[ℝ] ℂ) × ℂ => x.2.2) := contDiff_snd.snd
  have hap : ∀ {f : DSp × (ℂ →L[ℝ] ℂ) × ℂ → ℂ}, ContDiff ℝ ∞ f →
      ContDiff ℝ ∞ (fun x => ContinuousLinearMap.apply ℝ ℂ (f x)) :=
    fun hf => (ContinuousLinearMap.apply ℝ ℂ : ℂ →L[ℝ] _).contDiff.comp hf
  have hJ : ∀ L : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ),
      ContDiff ℝ ∞ (fun x : DSp × (ℂ →L[ℝ] ℂ) × ℂ => L.comp x.1) :=
    fun L => contDiff_const.clm_comp hD
  have hGy : ContDiff ℝ ∞ (fun x : DSp × (ℂ →L[ℝ] ℂ) × ℂ => x.2.1 x.2.2) := hG.clm_apply hy
  unfold PhiA
  exact (((hap hy).clm_comp (hJ J21L)).sub (hG.clm_comp ((hap hy).clm_comp (hJ J11L)))).add
    ((hap hGy).clm_comp (hJ J22L)) |>.sub (hG.clm_comp ((hap hGy).clm_comp (hJ J12L)))

lemma PhiB_contDiff : ContDiff ℝ ∞ PhiB := by
  have hD : ContDiff ℝ ∞ (fun x : DSp × (ℂ →L[ℝ] ℂ) => x.1) := contDiff_fst
  have hG : ContDiff ℝ ∞ (fun x : DSp × (ℂ →L[ℝ] ℂ) => compL ℝ ℂ ℂ ℂ x.2) :=
    (compL ℝ ℂ ℂ ℂ).contDiff.comp contDiff_snd
  unfold PhiB
  exact (contDiff_const.clm_comp hD).sub (hG.clm_comp (contDiff_const.clm_comp hD))

end

end FiniteEnergyPlane.B3E

/-! B3E layer S3b: bounded derivatives of the Hadamard-coefficient terms on the end. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

/-- Standing hypotheses of the end analysis. -/
structure EHyp (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (β : ContDiffBump (0 : ℂ)) (g ψ v : ℂ → ℂ) (r₁ δ : ℝ) (κ : ℂ) (b' : ℝ)
    (E : ℝ × ℝ → ℝ × ℝ) (S : ℝ) : Prop extends AHyp ρ b Jbar Jinf Sinf β g ψ r₁ δ κ b' where
  hψ : ContDiff ℝ ∞ ψ
  hv : ContDiff ℝ ∞ v
  hvr : ∀ z, ‖v z‖ ≤ r₁
  hvas : ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ)
  hrIn : r₁ < β.rIn
  hrOut : β.rOut ≤ ρ
  hL : LCData ψ κ b' E S

variable {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
  {Sinf : ℝ → Mat 1} {β : ContDiffBump (0 : ℂ)} {g ψ v : ℂ → ℂ} {r₁ δ : ℝ} {κ : ℂ} {b' : ℝ}
  {E : ℝ × ℝ → ℝ × ℝ} {S : ℝ}

/-- `ĥ = hd ∘ cyl`. -/
def hdc (g ψ v : ℂ → ℂ) (q : ℝ × ℝ) : ℂ := hd g ψ v (cylInf q.1 q.2)

/-- `ĝ ∘ Ψ`. -/
def gPs (g : ℂ → ℂ) (κ : ℂ) (E : ℝ × ℝ → ℝ × ℝ) (q : ℝ × ℝ) : ℂ :=
  g (cylInf (Psi κ E q).1 (Psi κ E q).2)

/-- The inner family `Y_θ = (Ψ, ĝ ∘ Ψ + θ ĥ)`. -/
def Yth (g ψ v : ℂ → ℂ) (κ : ℂ) (E : ℝ × ℝ → ℝ × ℝ) (θ : Icc (0 : ℝ) 1) (q : ℝ × ℝ) :
    ℝ × ℝ × ℂ :=
  ((Psi κ E q).1, (Psi κ E q).2, gPs g κ E q + (θ : ℝ) • hdc g ψ v q)

/-- `D_θ = ∂_w cylJ ∘ Y_θ`. -/
def Dth (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (g ψ v : ℂ → ℂ) (κ : ℂ) (E : ℝ × ℝ → ℝ × ℝ)
    (θ : Icc (0 : ℝ) 1) (q : ℝ × ℝ) : DSp := DwF Jbar (Yth g ψ v κ E θ q)

lemma Yth_eq (θ : Icc (0 : ℝ) 1) : Yth g ψ v κ E θ = fun q =>
    L3 q + L3 (cshift κ) + (L3 (E q) + I3 (gPs g κ E q + (θ : ℝ) • hdc g ψ v q)) := by
  funext q; simp [Yth, L3, I3, Psi]

/-- On the end, `ĝ ∘ Ψ + θ ĥ = (1 - θ) g(ψ z) + θ v z`. -/
lemma gPs_add (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) {s : ℝ} (hs : S ≤ s) (t : ℝ)
    (θ : Icc (0 : ℝ) 1) : ‖gPs g κ E (s, t) + (θ : ℝ) • hdc g ψ v (s, t)‖ ≤ r₁ := by
  have he := H.hL.heq s hs t
  have e : gPs g κ E (s, t) + (θ : ℝ) • hdc g ψ v (s, t) =
      (1 - (θ : ℝ)) • g (ψ (cylInf s t)) + (θ : ℝ) • v (cylInf s t) := by
    simp only [gPs, hdc, hd, ← he, smul_sub, sub_smul, one_smul]; abel
  rw [e]
  obtain ⟨θ, h0, h1⟩ := θ
  calc ‖(1 - θ) • g (ψ (cylInf s t)) + θ • v (cylInf s t)‖
      ≤ (1 - θ) * r₁ + θ * r₁ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, Real.norm_eq_abs]
        · rw [abs_of_nonneg (by linarith)]
          exact mul_le_mul_of_nonneg_left (H.hgr _) (by linarith)
        · rw [abs_of_nonneg h0]; exact mul_le_mul_of_nonneg_left (H.hvr _) h0
    _ = r₁ := by ring

lemma bdF_inner (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    BdF (fun (θ : Icc (0 : ℝ) 1) q => L3 (E q) + I3 (gPs g κ E q + (θ : ℝ) • hdc g ψ v q)) := by
  have hδ' : 0 ≤ -δ := by linarith [H.hδ]
  have hE : BdF (fun (_ : Icc (0 : ℝ) 1) q => E q) := bdF_of_bdH (bdH_of_expDecay H.hb'.le H.hL.hE)
  have hg : BdF (fun (_ : Icc (0 : ℝ) 1) q => gPs g κ E q) :=
    bdF_of_bdH (bdH_of_expDecay hδ' (gPsi_decay H.toAHyp H.hL))
  have hh : BdF (fun (_ : Icc (0 : ℝ) 1) q => hdc g ψ v q) :=
    bdF_of_bdH (bdH_of_expDecay hδ' (hd_decay H.toAHyp H.hvas))
  have hθ : BdF (fun (θ : Icc (0 : ℝ) 1) (_ : ℝ × ℝ) => (θ : ℝ)) :=
    bdF_const_family _ 1 fun θ => by
      obtain ⟨θ, h0, h1⟩ := θ; simp [abs_of_nonneg h0, h1]
  exact bdF_add (bdF_clm L3 hE)
    (bdF_clm I3 (bdF_add hg (bdF_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hθ hh)))

lemma hV_open (s₀ ρ : ℝ) : IsOpen (Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ) :=
  isOpen_Ioi.prod ((isOpen_univ (X := ℝ)).prod (isOpen_ball (x := (0 : ℂ))))

lemma dFc_contDiffOn {s₀ : ℝ}
    (hFc : ContDiffOn ℝ ∞ (Fc Jbar) (Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ)) :
    ContDiffOn ℝ ∞ (fun r => fderiv ℝ (Fc Jbar) r) (Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) :=
  hFc.fderiv_of_isOpen (m := ∞) (hV_open s₀ ρ) (by exact_mod_cast le_top)

/-- `fderiv cylJ ∘ Y_θ` has bounded derivatives on the end, uniformly in `θ ∈ [0, 1]`. -/
theorem EHyp.bdF_dFc (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    BdF (fun θ q => fderiv ℝ (Fc Jbar) (Yth g ψ v κ E θ q)) := by
  obtain ⟨s₀, hFc⟩ := Fc_contDiffOn H.hT
  have hI := bdF_inner H
  obtain ⟨a, haI⟩ := hI.1
  obtain ⟨BE, TE, -, hBE⟩ := (bdF_of_bdH (ι := Unit) (bdH_of_expDecay H.hb'.le H.hL.hE)).upTo 0
  have hEb : ∀ s ≥ TE, ∀ t, ‖E (s, t)‖ ≤ BE := fun s hs t => by
    simpa using hBE 0 le_rfl () s hs t
  have hδ' : 0 < -δ := by linarith [H.hδ]
  set c := cshift κ
  have hPsi1 : ∀ s ≥ TE, ∀ t, s + c.1 - BE ≤ (Psi κ E (s, t)).1 := by
    intro s hs t
    have h2 : |(E (s, t)).1| ≤ BE := (norm_fst_le (E (s, t))).trans (hEb s hs t)
    have := neg_abs_le (E (s, t)).1
    simp only [Psi, Prod.fst_add]
    linarith
  set A := max (max (max S TE) a) (s₀ - c.1 + BE + 1)
  have hAS : S ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hAT : TE ≤ A := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hAa : a ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
  have hA0 : s₀ - c.1 + BE + 1 ≤ A := le_max_right _ _
  have hYV : ∀ θ, ∀ s > A, ∀ t,
      Yth g ψ v κ E θ (s, t) ∈ Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ := by
    intro θ s hs t
    refine ⟨?_, mem_univ _, mem_ball_zero_iff.2 ((gPs_add H (hAS.trans hs.le) t θ).trans_lt
      H.hr₁)⟩
    have := hPsi1 s (hAT.trans hs.le) t
    show s₀ < (Psi κ E (s, t)).1
    linarith
  have hYs : ∀ θ, ContDiffOn ℝ ∞ (Yth g ψ v κ E θ) (Ioi A ×ˢ univ) := by
    intro θ
    rw [Yth_eq]
    exact ((L3.contDiff.add contDiff_const).contDiffOn).add ((haI θ).mono (hp_mono hAa))
  refine bdF_comp (fun r => fderiv ℝ (Fc Jbar) r) _ (hV_open s₀ ρ) (dFc_contDiffOn hFc)
    (Yth g ψ v κ E) A hYs hYV fun n => ?_
  obtain ⟨C, s₁, hC⟩ := Fc_bound_upTo H.hρ H.hb H.hT (n + 1)
  obtain ⟨Bi, Ti, -, hBi⟩ := hI.upTo n
  have hρ4 : 0 < ρ / 4 := by linarith [H.hρ]
  obtain ⟨s₂, hs₂⟩ := eventually_norm_le hδ' (gPsi_decay H.toAHyp H.hL) hρ4
  obtain ⟨s₃, hs₃⟩ := eventually_norm_le hδ' (hd_decay H.toAHyp H.hvas) hρ4
  refine ⟨C, ‖L3‖ + Bi, max (max (A + 1) (s₁ - c.1 + BE)) (max (max s₂ s₃) Ti),
    fun θ s hs t => ⟨fun i hi => ?_, fun i hi1 hi => ?_⟩⟩
  · have hsA : A + 1 ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
    have hs1 : s₁ - c.1 + BE ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
    have hs2 : s₂ ≤ s := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_right _ _)) hs
    have hs3 : s₃ ≤ s := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_right _ _)) hs
    rw [norm_iteratedFDeriv_fderiv]
    have hθ : ‖((θ : ℝ)) • hdc g ψ v (s, t)‖ ≤ ‖hdc g ψ v (s, t)‖ := by
      obtain ⟨θ, h0, h1⟩ := θ
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
      exact mul_le_of_le_one_left (norm_nonneg _) h1
    have hw : ‖gPs g κ E (s, t) + (θ : ℝ) • hdc g ψ v (s, t)‖ ≤ ρ / 2 := by
      have := hs₂ s hs2 t
      have := hs₃ s hs3 t
      simp only [gPs, hdc] at *
      linarith [norm_add_le (g (cylInf (Psi κ E (s, t)).1 (Psi κ E (s, t)).2))
        ((θ : ℝ) • hd g ψ v (cylInf s t))]
    have hσ1 : s₁ ≤ (Psi κ E (s, t)).1 := by
      have := hPsi1 s (hAT.trans (by linarith)) t; linarith
    exact hC _ hσ1 _ _ (mem_closedBall_zero_iff.2 hw) (i + 1) (by omega)
  · have hsA : A + 1 ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
    have hsT : Ti ≤ s := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hs)
    have has : a < s := by linarith
    rw [Yth_eq]
    refine (norm_iteratedFDeriv_affine_add_le L3 (L3 c) _ (haI θ) has t hi1).trans ?_
    gcongr
    exact hBi i hi θ s hsT t

end

end FiniteEnergyPlane.B3E

/-! B3E layer S3c: the cylindrical integrand families are bounded. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

variable {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
  {Sinf : ℝ → Mat 1} {β : ContDiffBump (0 : ℂ)} {g ψ v : ℂ → ℂ} {r₁ δ : ℝ} {κ : ℂ} {b' : ℝ}
  {E : ℝ × ℝ → ℝ × ℝ} {S : ℝ}

/-- Precomposition with `I3`. -/
def LI3 : ((ℝ × ℝ × ℂ) →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ)) →L[ℝ] (ℂ →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ)) :=
  (compL ℝ ℂ (ℝ × ℝ × ℂ) (ℂ × ℂ →L[ℝ] ℂ × ℂ)).flip I3

lemma LI3_apply (M : (ℝ × ℝ × ℂ) →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ)) : LI3 M = M.comp I3 := rfl

set_option synthInstance.maxHeartbeats 200000 in
theorem EHyp.bdF_Dth (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    BdF (Dth Jbar g ψ v κ E) := by
  have h := bdF_clm (F := (ℝ × ℝ × ℂ) →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ)) (G := DSp) LI3 H.bdF_dFc
  exact h

lemma EHyp.bdF_GPsi (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    BdF (fun (_ : Icc (0 : ℝ) 1) q => Ghat g (Psi κ E q)) :=
  bdF_of_bdH (bdH_of_expDecay (by linarith [H.hδ]) (GPsi_decay H.toAHyp H.hL))

lemma EHyp.bdF_Rr (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    BdF (fun (_ : Icc (0 : ℝ) 1) q => Rr E q) := by
  have h1 := bdH_add (bdH_of_expDecay H.hb'.le (Rr_decay H.hL.hE)) (bdH_const (1 : ℂ))
  refine bdF_of_bdH ?_
  simpa using h1

/-- The cylindrical `KA`-integrand family. -/
def QA (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (g ψ v : ℂ → ℂ) (κ : ℂ) (E : ℝ × ℝ → ℝ × ℝ)
    (θ : Icc (0 : ℝ) 1) (q : ℝ × ℝ) : ℂ →L[ℝ] ℂ :=
  PhiA (Dth Jbar g ψ v κ E θ q, Ghat g (Psi κ E q), Rr E q)

/-- The cylindrical `KB`-integrand family. -/
def QB (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (g ψ v : ℂ → ℂ) (κ : ℂ) (E : ℝ × ℝ → ℝ × ℝ)
    (θ : Icc (0 : ℝ) 1) (q : ℝ × ℝ) : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  PhiB (Dth Jbar g ψ v κ E θ q, Ghat g (Psi κ E q))

theorem EHyp.bdF_QA (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    BdF (QA Jbar g ψ v κ E) :=
  bdF_comp_smooth PhiA PhiA_contDiff (bdF_prod H.bdF_Dth (bdF_prod H.bdF_GPsi H.bdF_Rr))

theorem EHyp.bdF_QB (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    BdF (QB Jbar g ψ v κ E) :=
  bdF_comp_smooth PhiB PhiB_contDiff (bdF_prod H.bdF_Dth H.bdF_GPsi)

/-- `Ψ₁` is eventually above any level. -/
lemma Psi_fst_ge (hE : ExpDecayCInfty E b') (hb' : 0 < b') (T : ℝ) :
    ∃ A : ℝ, ∀ s ≥ A, ∀ t : ℝ, T ≤ (Psi κ E (s, t)).1 := by
  obtain ⟨BE, TE, -, hBE⟩ := (bdH_of_expDecay hb'.le hE).upTo 0
  refine ⟨max TE (T - (cshift κ).1 + BE), fun s hs t => ?_⟩
  have h0 := hBE 0 le_rfl s (le_of_max_le_left hs) t
  rw [norm_iteratedFDeriv_zero] at h0
  have h2 : |(E (s, t)).1| ≤ BE := (norm_fst_le (E (s, t))).trans h0
  have := neg_abs_le (E (s, t)).1
  have h3 := le_of_max_le_right hs
  simp only [Psi, Prod.fst_add]
  linarith

/-- The plane-side `KA`-integrand, applied to `Dψ(z)(2πz)`. -/
def PAp (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (β : ContDiffBump (0 : ℂ)) (g ψ v : ℂ → ℂ)
    (p : ℝ × ℝ) (θ : ℝ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.apply ℝ ℂ (fderiv ℝ ψ (cylInf p.1 p.2) (lam p.1 p.2))).comp
    (fderiv ℝ (fun a => Afun Jbar β g (ψ (cylInf p.1 p.2), a)) (θ • hd g ψ v (cylInf p.1 p.2)))

/-- The plane-side `KB`-integrand. -/
def PBp (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (β : ContDiffBump (0 : ℂ)) (g ψ v : ℂ → ℂ)
    (p : ℝ × ℝ) (θ : ℝ) : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  fderiv ℝ (fun a => Bfun Jbar β g (ψ (cylInf p.1 p.2), a)) (θ • hd g ψ v (cylInf p.1 p.2))

lemma EHyp.rIn_le (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) : β.rIn ≤ ρ :=
  β.rIn_lt_rOut.le.trans H.hrOut

lemma EHyp.hJ (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    ContDiffOn ℝ ∞ Jbar (univ ×ˢ ball (0 : ℂ) ρ) := H.hT.1

/-- Far out on the end, the plane-side integrands are the cylindrical ones. -/
theorem EHyp.PAp_PBp_eq (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    ∃ S' : ℝ, ∀ s > S', ∀ t : ℝ, ∀ θ (hθ : θ ∈ Icc (0 : ℝ) 1),
      PAp Jbar β g ψ v (s, t) θ = QA Jbar g ψ v κ E ⟨θ, hθ⟩ (s, t) ∧
      PBp Jbar β g ψ v (s, t) θ = QB Jbar g ψ v κ E ⟨θ, hθ⟩ (s, t) := by
  obtain ⟨s₀, hFc⟩ := Fc_contDiffOn H.hT
  obtain ⟨S₁, hR⟩ := Rr_eq H.hψ H.hL
  obtain ⟨A, hA⟩ := Psi_fst_ge (κ := κ) H.hL.hE H.hb' (s₀ + 1)
  refine ⟨max (max S₁ S) A, fun s hs t θ hθ => ?_⟩
  have hS₁ : S₁ < s := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hS : S ≤ s := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hs.le
  have hAs : A ≤ s := (le_max_right _ _).trans hs.le
  have he := H.hL.heq s hS t
  have hσ : s₀ < (Psi κ E (s, t)).1 := by linarith [hA s hAs t]
  have ha : ‖g (cylInf (Psi κ E (s, t)).1 (Psi κ E (s, t)).2) +
      θ • hd g ψ v (cylInf s t)‖ < β.rIn :=
    lt_of_le_of_lt (gPs_add H hS t ⟨θ, hθ⟩) (lt_of_lt_of_le (lt_of_le_of_lt le_rfl H.hrIn) le_rfl)
  have key := fun u y => fderiv_Afun_Bfun_cyl (β := β) hFc H.hg H.rIn_le hσ ha u y
  refine ⟨ContinuousLinearMap.ext fun u => ?_, ContinuousLinearMap.ext fun u =>
    ContinuousLinearMap.ext fun y => ?_⟩
  · simp only [PAp, comp_apply, ContinuousLinearMap.apply_apply, he, (key u _).1]
    rw [QA, PhiA_apply, ← hR s hS₁ t]
    rfl
  · simp only [PBp, he, (key u y).2]
    rw [QB, PhiB_apply]
    rfl

lemma EHyp.PAp_contDiff (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    ContDiff ℝ ∞ (Function.uncurry (PAp Jbar β g ψ v)) := by
  have hA := (Afun_Bfun_contDiff H.hJ H.hrOut H.hg).1
  have hc : ContDiff ℝ ∞ (fun x : (ℝ × ℝ) × ℝ => cylInf x.1.1 x.1.2) :=
    cyl_contDiff.comp contDiff_fst
  have hhd : ContDiff ℝ ∞ (hd g ψ v) := H.hv.sub (H.hg.comp H.hψ)
  have h1 : ContDiff ℝ ∞ (fun x : (ℝ × ℝ) × ℝ =>
      fderiv ℝ (fun a => Afun Jbar β g (ψ (cylInf x.1.1 x.1.2), a))
        (x.2 • hd g ψ v (cylInf x.1.1 x.1.2))) := by
    refine ContDiff.fderiv (m := ∞) ?_ (contDiff_snd.smul (hhd.comp hc)) (by simp)
    exact hA.comp ((H.hψ.comp (hc.comp contDiff_fst)).prodMk contDiff_snd)
  have hl : ContDiff ℝ ∞ (fun x : (ℝ × ℝ) × ℝ => lam x.1.1 x.1.2) :=
    contDiff_const.mul hc
  have h2 : ContDiff ℝ ∞ (fun x : (ℝ × ℝ) × ℝ =>
      fderiv ℝ ψ (cylInf x.1.1 x.1.2) (lam x.1.1 x.1.2)) :=
    ((H.hψ.fderiv_right (m := ∞) (by simp)).comp hc).clm_apply hl
  have h3 : ContDiff ℝ ∞ (fun x : (ℝ × ℝ) × ℝ =>
      ContinuousLinearMap.apply ℝ ℂ (fderiv ℝ ψ (cylInf x.1.1 x.1.2) (lam x.1.1 x.1.2))) :=
    (ContinuousLinearMap.apply ℝ ℂ : ℂ →L[ℝ] _).contDiff.comp h2
  exact h3.clm_comp h1

lemma EHyp.PBp_contDiff (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    ContDiff ℝ ∞ (Function.uncurry (PBp Jbar β g ψ v)) := by
  have hB := (Afun_Bfun_contDiff H.hJ H.hrOut H.hg).2
  have hc : ContDiff ℝ ∞ (fun x : (ℝ × ℝ) × ℝ => cylInf x.1.1 x.1.2) :=
    cyl_contDiff.comp contDiff_fst
  have hhd : ContDiff ℝ ∞ (hd g ψ v) := H.hv.sub (H.hg.comp H.hψ)
  refine ContDiff.fderiv (m := ∞) ?_ (contDiff_snd.smul (hhd.comp hc)) (by simp)
  exact hB.comp ((H.hψ.comp (hc.comp contDiff_fst)).prodMk contDiff_snd)

/-- Transfer of family bounds through the far-out identity. -/
lemma bdH_integral_of_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (P : ℝ × ℝ → ℝ → F) (hP : ContDiff ℝ ∞ (Function.uncurry P))
    (Q : Icc (0 : ℝ) 1 → ℝ × ℝ → F) (hQ : BdF Q) (S' : ℝ)
    (heq : ∀ s > S', ∀ t : ℝ, ∀ θ (hθ : θ ∈ Icc (0 : ℝ) 1), P (s, t) θ = Q ⟨θ, hθ⟩ (s, t)) :
    BdH (fun p => ∫ θ in (0 : ℝ)..1, P p θ) := by
  refine bdH_integral P hP fun m => ?_
  obtain ⟨C, s₁, hC⟩ := hQ.2 m
  refine ⟨C, max s₁ (S' + 1), fun θ hθ s hs t => ?_⟩
  have hU : IsOpen (Ioi S' ×ˢ (univ : Set ℝ)) := hp_open S'
  have hmem : ((s, t) : ℝ × ℝ) ∈ Ioi S' ×ˢ (univ : Set ℝ) :=
    ⟨show S' < s by linarith [le_max_right s₁ (S' + 1)], mem_univ _⟩
  rw [BT.iteratedFDeriv_congr_open hU (g := Q ⟨θ, hθ⟩)
    (fun q hq => by obtain ⟨q1, q2⟩ := q; exact heq q1 hq.1 q2 θ hθ) hmem m]
  exact hC _ s (le_of_max_le_left hs) t

theorem EHyp.bdH_XA (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    BdH (fun p => ∫ θ in (0 : ℝ)..1, PAp Jbar β g ψ v p θ) := by
  obtain ⟨S', h⟩ := H.PAp_PBp_eq
  exact bdH_integral_of_eq _ H.PAp_contDiff _ H.bdF_QA S' fun s hs t θ hθ => (h s hs t θ hθ).1

theorem EHyp.bdH_XB (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    BdH (fun p => ∫ θ in (0 : ℝ)..1, PBp Jbar β g ψ v p θ) := by
  obtain ⟨S', h⟩ := H.PAp_PBp_eq
  exact bdH_integral_of_eq _ H.PBp_contDiff _ H.bdF_QB S' fun s hs t θ hθ => (h s hs t θ hθ).2

end

end FiniteEnergyPlane.B3E

/-! B3E layer S3d: tools for the `C⁰` limit of the `KA`-term. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma ExpDecayCInfty.c0 {f : ℝ × ℝ → F} {b : ℝ} (hf : ExpDecayCInfty f b) :
    ∃ C s₁ : ℝ, 0 ≤ C ∧ ∀ s ≥ s₁, ∀ t : ℝ, ‖f (s, t)‖ ≤ C * Real.exp (-(b * s)) := by
  obtain ⟨C, s₁, h⟩ := hf.2 0
  refine ⟨|C|, s₁, abs_nonneg _, fun s hs t => ?_⟩
  have := h s hs t
  rw [norm_iteratedFDeriv_zero] at this
  exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)

lemma exp_rate_le {d b s : ℝ} (hd : d ≤ b) (hs : 0 ≤ s) :
    Real.exp (-(b * s)) ≤ Real.exp (-(d * s)) :=
  Real.exp_le_exp.2 (by nlinarith)

/-- A `C¹` map on a finite-dimensional space is Lipschitz on balls. -/
lemma lip_on_ball {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (Φ : X → F) (hΦ : ContDiff ℝ ∞ Φ) (K : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : X, ‖x‖ ≤ K → ‖y‖ ≤ K → ‖Φ x - Φ y‖ ≤ L * ‖x - y‖ := by
  have hK : IsCompact (closedBall (0 : X) K) := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((hΦ.continuous_fderiv (by simp)).continuousOn)
  refine ⟨|C|, abs_nonneg _, fun x y hx hy => ?_⟩
  have hd : ∀ z ∈ closedBall (0 : X) K, DifferentiableAt ℝ Φ z :=
    fun z _ => hΦ.differentiable (by simp) z
  have hb : ∀ z ∈ closedBall (0 : X) K, ‖fderiv ℝ Φ z‖ ≤ |C| :=
    fun z hz => (hC z hz).trans (le_abs_self _)
  exact (convex_closedBall (0 : X) K).norm_image_sub_le_of_norm_fderiv_le hd hb
    (mem_closedBall_zero_iff.2 hy) (mem_closedBall_zero_iff.2 hx)

variable {ρ : ℝ} {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}

/-- The `w`-partial derivative of `Jinf`. -/
def PhiJ (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (p : ℝ × ℂ) : DSp :=
  (fderiv ℝ Jinf p).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)

lemma hO2 (ρ : ℝ) : IsOpen ((univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ) :=
  (isOpen_univ : IsOpen (univ : Set ℝ)).prod isOpen_ball

lemma PhiJ_contDiffOn (hJi : ContDiffOn ℝ ∞ Jinf (univ ×ˢ ball (0 : ℂ) ρ)) :
    ContDiffOn ℝ ∞ (PhiJ Jinf) (univ ×ˢ ball (0 : ℂ) ρ) := by
  have h := hJi.fderiv_of_isOpen (m := ∞) (hO2 ρ) (by exact_mod_cast le_top)
  exact h.clm_comp contDiffOn_const

lemma PhiJ_per (hper : ∀ (t : ℝ) (w : ℂ), Jinf (t + 1, w) = Jinf (t, w)) (τ : ℝ) (w : ℂ) :
    PhiJ Jinf (τ + 1, w) = PhiJ Jinf (τ, w) := by
  have e : Jinf = fun p : ℝ × ℂ => Jinf (p + ((1 : ℝ), (0 : ℂ))) := by
    funext p; obtain ⟨τ, w⟩ := p; simp [hper]
  unfold PhiJ
  congr 1
  conv_rhs => rw [e]
  rw [fderiv_comp_add_right]
  simp

lemma Kd_eq_PhiJ (hJi : ContDiffOn ℝ ∞ Jinf (univ ×ˢ ball (0 : ℂ) ρ)) (hρ : 0 < ρ) (τ : ℝ) :
    Kd Jinf τ = PhiJ Jinf (τ, 0) := by
  have hd : DifferentiableAt ℝ Jinf (τ, 0) :=
    ((hJi.contDiffAt ((hO2 ρ).mem_nhds ⟨mem_univ _, mem_ball_self hρ⟩)).differentiableAt
      (by simp))
  have hin : HasFDerivAt (fun w : ℂ => ((τ, w) : ℝ × ℂ)) (ContinuousLinearMap.inr ℝ ℝ ℂ) 0 := by
    have := ((ContinuousLinearMap.inr ℝ ℝ ℂ).hasFDerivAt (x := (0 : ℂ))).const_add ((τ, 0) : ℝ × ℂ)
    simpa using this
  have := hd.hasFDerivAt.comp (0 : ℂ) (by simpa using hin)
  exact this.fderiv

lemma Minf_eq_PhiA (τ : ℝ) : Minf Jinf τ = PhiA (Kd Jinf τ, 0, 1) := by
  ext1 u
  rw [PhiA_apply]
  simp [Minf, Ablk, J21]

end

end FiniteEnergyPlane.B3E

/-! B3E layer S3e: the `C⁰` limit of the `KA`-term and its `C^∞` decay. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The common decay rate. -/
def d0 (b b' δ : ℝ) : ℝ := min (min b b') (-δ)

lemma d0_le_b {b b' δ : ℝ} : d0 b b' δ ≤ b := (min_le_left _ _).trans (min_le_left _ _)
lemma d0_le_b' {b b' δ : ℝ} : d0 b b' δ ≤ b' := (min_le_left _ _).trans (min_le_right _ _)
lemma d0_le_δ {b b' δ : ℝ} : d0 b b' δ ≤ -δ := min_le_right _ _

lemma c0_at {f : ℝ × ℝ → F} {e d : ℝ} (hf : ExpDecayCInfty f e) (hd : d ≤ e) :
    ∃ C s₁ : ℝ, 0 ≤ C ∧ ∀ s ≥ s₁, ∀ t : ℝ, ‖f (s, t)‖ ≤ C * Real.exp (-(d * s)) := by
  obtain ⟨C, s₁, hC, h⟩ := ExpDecayCInfty.c0 hf
  exact ⟨C, max s₁ 0, hC, fun s hs t => (h s (le_of_max_le_left hs) t).trans
    (mul_le_mul_of_nonneg_left (exp_rate_le hd (le_of_max_le_right hs)) hC)⟩

lemma norm_triple_le {A B C : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [NormedAddCommGroup C] (a : A) (b : B) (c : C) : ‖(a, b, c)‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le (by linarith [norm_nonneg b, norm_nonneg c])
    (max_le (by linarith [norm_nonneg a, norm_nonneg c]) (by linarith [norm_nonneg a, norm_nonneg b]))

variable {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
  {Sinf : ℝ → Mat 1} {β : ContDiffBump (0 : ℂ)} {g ψ v : ℂ → ℂ} {r₁ δ : ℝ} {κ : ℂ} {b' : ℝ}
  {E : ℝ × ℝ → ℝ × ℝ} {S : ℝ}

lemma EHyp.d0_pos (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) : 0 < d0 b b' δ :=
  lt_min (lt_min H.hb H.hb') (by linarith [H.hδ])

lemma Psi_fst_lb (hE : ExpDecayCInfty E b') (hb' : 0 < b') :
    ∃ M A : ℝ, ∀ s ≥ A, ∀ t : ℝ, s - M ≤ (Psi κ E (s, t)).1 := by
  obtain ⟨BE, TE, -, hBE⟩ := (bdH_of_expDecay hb'.le hE).upTo 0
  refine ⟨BE - (cshift κ).1, TE, fun s hs t => ?_⟩
  have h0 := hBE 0 le_rfl s hs t
  rw [norm_iteratedFDeriv_zero] at h0
  have h2 : |(E (s, t)).1| ≤ BE := (norm_fst_le (E (s, t))).trans h0
  have := neg_abs_le (E (s, t)).1
  simp only [Psi, Prod.fst_add]
  linarith

/-- Projection to `(τ, w)`. -/
def pr3 : ℝ × ℝ × ℂ →L[ℝ] ℝ × ℂ := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)

/-- `∂_w cylJ` splits into the tube difference and the limit. -/
lemma DwF_split {s₀ : ℝ} (hfd : ContDiffOn ℝ ∞ (fd Jbar Jinf) (Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ))
    (hJi : ContDiffOn ℝ ∞ Jinf (univ ×ˢ ball (0 : ℂ) ρ)) {Y : ℝ × ℝ × ℂ}
    (hY : Y ∈ Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) :
    DwF Jbar Y = (fderiv ℝ (fd Jbar Jinf) Y).comp I3 + PhiJ Jinf (Y.2.1, Y.2.2) := by
  have hsplit : Fc Jbar = fun r => fd Jbar Jinf r + Jinf (pr3 r) := by
    funext r; simp [Fc, fd, pr3]
  have h1 : DifferentiableAt ℝ (fd Jbar Jinf) Y :=
    (hfd.contDiffAt ((hV_open s₀ ρ).mem_nhds hY)).differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ Jinf (pr3 Y) :=
    (hJi.contDiffAt ((hO2 ρ).mem_nhds (show pr3 Y ∈ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ from
      ⟨mem_univ _, hY.2.2⟩))).differentiableAt (by simp)
  have h3 : HasFDerivAt (fun r => Jinf (pr3 r)) ((fderiv ℝ Jinf (pr3 Y)).comp pr3) Y :=
    h2.hasFDerivAt.comp Y pr3.hasFDerivAt
  have h4 : HasFDerivAt (Fc Jbar)
      (fderiv ℝ (fd Jbar Jinf) Y + (fderiv ℝ Jinf (pr3 Y)).comp pr3) Y := by
    rw [hsplit]; exact h1.hasFDerivAt.add h3
  unfold DwF PhiJ
  rw [h4.fderiv]
  ext1 w
  simp [pr3, I3]

theorem EHyp.Dth_sub_Kd (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    ∃ C s₁ : ℝ, 0 ≤ C ∧ ∀ s ≥ s₁, ∀ t : ℝ, ∀ θ : Icc (0 : ℝ) 1,
      ‖Dth Jbar g ψ v κ E θ (s, t) - Kd Jinf (t + (cshift κ).2)‖ ≤
        C * Real.exp (-(d0 b b' δ * s)) := by
  obtain ⟨-, -, -, hJi, hper, hdec, -, -⟩ := H.hT
  have hdec' : ExpDecayCInftyTube (fd Jbar Jinf) ρ b := hdec
  obtain ⟨⟨s₀, hfd⟩, hdb⟩ := hdec'
  obtain ⟨Cf, sf, hCf⟩ := hdb 1
  obtain ⟨M, A, hMA⟩ := Psi_fst_lb (κ := κ) H.hL.hE H.hb'
  obtain ⟨A2, hA2⟩ := Psi_fst_ge (κ := κ) H.hL.hE H.hb' (max (s₀ + 1) sf)
  obtain ⟨Lp, hLp⟩ := per_lip (PhiJ Jinf) H.hr₁ (PhiJ_contDiffOn hJi) (PhiJ_per hper)
  obtain ⟨CE, sE, hCE0, hCE⟩ := c0_at H.hL.hE (d0_le_b' (b := b) (δ := δ))
  obtain ⟨Cg, sg, hCg0, hCg⟩ := c0_at (gPsi_decay H.toAHyp H.hL) (d0_le_δ (b := b) (b' := b'))
  obtain ⟨Ch, sh, hCh0, hCh⟩ := c0_at (hd_decay H.toAHyp H.hvas) (d0_le_δ (b := b) (b' := b'))
  have hr0 : 0 ≤ r₁ := (norm_nonneg _).trans (H.hgr 0)
  refine ⟨|Cf| * ‖I3‖ * Real.exp (b * M) + |Lp| * (CE + Cg + Ch),
    max (max (max A A2) (max sE sg)) (max (max sh S) 0), by positivity, fun s hs t θ => ?_⟩
  have hsA : A ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hs)
  have hsA2 : A2 ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hs)
  have hsE : sE ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hs)
  have hsg : sg ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hs)
  have hsh : sh ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) hs)
  have hsS : S ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) hs)
  have hs0 : 0 ≤ s := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hs)
  set σ' := (Psi κ E (s, t)).1 with hσ'
  set τ' := (Psi κ E (s, t)).2 with hτ'
  set w := gPs g κ E (s, t) + (θ : ℝ) • hdc g ψ v (s, t) with hw
  have hwr : ‖w‖ ≤ r₁ := gPs_add H hsS t θ
  have hwb : w ∈ ball (0 : ℂ) ρ := mem_ball_zero_iff.2 (hwr.trans_lt H.hr₁)
  have hσA2 := hA2 s hsA2 t
  have hσs₀ : s₀ < σ' := by linarith [le_max_left (s₀ + 1) sf]
  have hσsf : sf ≤ σ' := le_trans (le_max_right _ _) hσA2
  have hY : ((σ', τ', w) : ℝ × ℝ × ℂ) ∈ Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ :=
    ⟨hσs₀, mem_univ _, hwb⟩
  have hD : Dth Jbar g ψ v κ E θ (s, t) = DwF Jbar (σ', τ', w) := rfl
  rw [hD, DwF_split hfd hJi hY, Kd_eq_PhiJ hJi H.hρ]
  have e1 : (fderiv ℝ (fd Jbar Jinf) (σ', τ', w)).comp I3 + PhiJ Jinf (τ', w) -
      PhiJ Jinf (t + (cshift κ).2, 0) = (fderiv ℝ (fd Jbar Jinf) (σ', τ', w)).comp I3 +
      (PhiJ Jinf (τ', w) - PhiJ Jinf (t + (cshift κ).2, 0)) := by abel
  rw [e1]
  refine (norm_add_le ((fderiv ℝ (fd Jbar Jinf) (σ', τ', w)).comp I3)
    (PhiJ Jinf (τ', w) - PhiJ Jinf (t + (cshift κ).2, 0))).trans ?_
  have hexp : Real.exp (-(b * σ')) ≤ Real.exp (b * M) * Real.exp (-(d0 b b' δ * s)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := hMA s hsA t
    have hdb : d0 b b' δ ≤ b := d0_le_b
    linarith [mul_le_mul_of_nonneg_left this H.hb.le, mul_le_mul_of_nonneg_right hdb hs0]
  have t1 : ‖(fderiv ℝ (fd Jbar Jinf) (σ', τ', w)).comp I3‖ ≤
      |Cf| * ‖I3‖ * Real.exp (b * M) * Real.exp (-(d0 b b' δ * s)) := by
    refine (opNorm_comp_le _ _).trans ?_
    have hf1 : ‖fderiv ℝ (fd Jbar Jinf) (σ', τ', w)‖ ≤ Cf * Real.exp (-(b * σ')) := by
      have := hCf σ' hσsf τ' w hwb
      rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at this
    have hf2 : ‖fderiv ℝ (fd Jbar Jinf) (σ', τ', w)‖ ≤
        |Cf| * (Real.exp (b * M) * Real.exp (-(d0 b b' δ * s))) :=
      hf1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_left hexp (abs_nonneg _)))
    calc ‖fderiv ℝ (fd Jbar Jinf) (σ', τ', w)‖ * ‖I3‖
        ≤ |Cf| * (Real.exp (b * M) * Real.exp (-(d0 b b' δ * s))) * ‖I3‖ :=
          mul_le_mul_of_nonneg_right hf2 (norm_nonneg _)
      _ = _ := by ring
  have t2 : ‖PhiJ Jinf (τ', w) - PhiJ Jinf (t + (cshift κ).2, 0)‖ ≤
      |Lp| * (CE + Cg + Ch) * Real.exp (-(d0 b b' δ * s)) := by
    have hl := hLp (τ', w) (t + (cshift κ).2, 0) hwr (by simpa using hr0)
    have hdiff : ((τ', w) : ℝ × ℂ) - (t + (cshift κ).2, 0) = ((E (s, t)).2, w) := by
      simp only [Prod.mk_sub_mk, sub_zero, hτ', Psi, Prod.snd_add]
      congr 1; ring
    rw [hdiff] at hl
    have hn : ‖(((E (s, t)).2, w) : ℝ × ℂ)‖ ≤ (CE + Cg + Ch) * Real.exp (-(d0 b b' δ * s)) := by
      rw [Prod.norm_def]
      have e2 : ‖(E (s, t)).2‖ ≤ CE * Real.exp (-(d0 b b' δ * s)) :=
        (_root_.norm_snd_le _).trans (hCE s hsE t)
      have e3 : ‖w‖ ≤ (Cg + Ch) * Real.exp (-(d0 b b' δ * s)) := by
        have hθ : ‖(θ : ℝ) • hdc g ψ v (s, t)‖ ≤ ‖hdc g ψ v (s, t)‖ := by
          obtain ⟨θ, h0, h1⟩ := θ
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
          exact mul_le_of_le_one_left (norm_nonneg _) h1
        have := hCg s hsg t
        have := hCh s hsh t
        calc ‖w‖ ≤ ‖gPs g κ E (s, t)‖ + ‖hdc g ψ v (s, t)‖ :=
              (norm_add_le _ _).trans (add_le_add le_rfl hθ)
          _ ≤ _ := by simp only [gPs, hdc] at *; linarith
      have hx : 0 ≤ Real.exp (-(d0 b b' δ * s)) := (Real.exp_pos _).le
      exact max_le (e2.trans (by linarith [mul_nonneg hCg0 hx, mul_nonneg hCh0 hx]))
        (e3.trans (by linarith [mul_nonneg hCE0 hx]))
    calc _ ≤ Lp * ‖(((E (s, t)).2, w) : ℝ × ℂ)‖ := hl
      _ ≤ |Lp| * ‖(((E (s, t)).2, w) : ℝ × ℂ)‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ ≤ |Lp| * ((CE + Cg + Ch) * Real.exp (-(d0 b b' δ * s))) :=
          mul_le_mul_of_nonneg_left hn (abs_nonneg _)
      _ = _ := by ring
  calc _ ≤ |Cf| * ‖I3‖ * Real.exp (b * M) * Real.exp (-(d0 b b' δ * s)) +
        |Lp| * (CE + Cg + Ch) * Real.exp (-(d0 b b' δ * s)) := add_le_add t1 t2
    _ = _ := by ring

set_option synthInstance.maxHeartbeats 400000 in
theorem EHyp.QA_sub_Minf (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    ∃ C s₁ : ℝ, 0 ≤ C ∧ ∀ s ≥ s₁, ∀ t : ℝ, ∀ θ : Icc (0 : ℝ) 1,
      ‖QA Jbar g ψ v κ E θ (s, t) - Minf Jinf (t + (cshift κ).2)‖ ≤
        C * Real.exp (-(d0 b b' δ * s)) := by
  obtain ⟨-, -, -, hJi, hper, -, -, -⟩ := H.hT
  obtain ⟨Kx, Tx, hKx0, hKx⟩ := (bdF_prod H.bdF_Dth (bdF_prod H.bdF_GPsi H.bdF_Rr)).upTo 0
  obtain ⟨CK, hCK⟩ := per_bound (PhiJ Jinf) H.hρ (PhiJ_contDiffOn hJi) (PhiJ_per hper) 0
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Kx + |CK| + 1 := ⟨_, rfl⟩
  obtain ⟨L, hL0, hL⟩ := lip_on_ball PhiA PhiA_contDiff K
  obtain ⟨CD, sD, hCD0, hCD⟩ := H.Dth_sub_Kd
  obtain ⟨CG, sG, hCG0, hCG⟩ := c0_at (GPsi_decay H.toAHyp H.hL) (d0_le_δ (b := b) (b' := b'))
  obtain ⟨CR, sR, hCR0, hCR⟩ := c0_at (Rr_decay H.hL.hE) (d0_le_b' (b := b) (δ := δ))
  refine ⟨L * (CD + CG + CR), max (max Tx sD) (max sG sR), by positivity, fun s hs t θ => ?_⟩
  have hTx : Tx ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hsD : sD ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hsG : sG ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hsR : sR ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  obtain ⟨x, hx⟩ : ∃ x : DSp × (ℂ →L[ℝ] ℂ) × ℂ,
      x = (Dth Jbar g ψ v κ E θ (s, t), Ghat g (Psi κ E (s, t)), Rr E (s, t)) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : DSp × (ℂ →L[ℝ] ℂ) × ℂ,
      y = (Kd Jinf (t + (cshift κ).2), 0, 1) := ⟨_, rfl⟩
  have hxK : ‖x‖ ≤ K := by
    have := hKx 0 le_rfl θ s hTx t
    rw [norm_iteratedFDeriv_zero, ← hx] at this
    exact this.trans (by rw [hK]; linarith [abs_nonneg CK])
  have hyK : ‖y‖ ≤ K := by
    have h1 : ‖Kd Jinf (t + (cshift κ).2)‖ ≤ |CK| := by
      rw [Kd_eq_PhiJ hJi H.hρ]
      have := hCK (t + (cshift κ).2) 0 (by simp) 0 le_rfl
      rw [norm_iteratedFDeriv_zero] at this
      exact this.trans (le_abs_self _)
    rw [hy]
    refine (norm_triple_le (A := DSp) (B := ℂ →L[ℝ] ℂ) (C := ℂ) _ _ _).trans ?_
    simp only [norm_zero, norm_one]
    rw [hK]; linarith
  rw [QA, Minf_eq_PhiA, ← hx, ← hy]
  refine (hL x y hxK hyK).trans ?_
  have hxy : ‖x - y‖ ≤ (CD + CG + CR) * Real.exp (-(d0 b b' δ * s)) := by
    have e : x - y = (Dth Jbar g ψ v κ E θ (s, t) - Kd Jinf (t + (cshift κ).2),
        Ghat g (Psi κ E (s, t)) - 0, Rr E (s, t) - 1) := by
      rw [hx, hy]; rfl
    rw [e]
    refine (norm_triple_le (A := DSp) (B := ℂ →L[ℝ] ℂ) (C := ℂ) _ _ _).trans ?_
    have := hCD s hsD t θ
    have := hCG s hsG t
    have := hCR s hsR t
    rw [sub_zero]
    linarith
  calc L * ‖x - y‖ ≤ L * ((CD + CG + CR) * Real.exp (-(d0 b b' δ * s))) :=
        mul_le_mul_of_nonneg_left hxy hL0
    _ = _ := by ring

lemma norm_integral_sub_const_le [CompleteSpace F] (f : ℝ → F) (hf : Continuous f) (c : F)
    (C : ℝ) (h : ∀ θ ∈ Icc (0 : ℝ) 1, ‖f θ - c‖ ≤ C) : ‖(∫ θ in (0 : ℝ)..1, f θ) - c‖ ≤ C := by
  have e : (∫ θ in (0 : ℝ)..1, f θ) - c = ∫ θ in (0 : ℝ)..1, (f θ - c) := by
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp
  rw [e]
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := C)
    (f := fun θ => f θ - c) (fun θ hθ => by
      rw [uIoc_of_le zero_le_one] at hθ; exact h θ (Ioc_subset_Icc_self hθ))
  simpa using h2

/-- The `C⁰` limit of `X = ∫ KA`-integrand. -/
theorem EHyp.XA_c0 (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖(∫ θ in (0 : ℝ)..1, PAp Jbar β g ψ v (s, t) θ) - Minf Jinf (t + (cshift κ).2)‖ ≤
        C * Real.exp (-(d0 b b' δ * s)) := by
  obtain ⟨S', hS'⟩ := H.PAp_PBp_eq
  obtain ⟨C, s₁, -, hC⟩ := H.QA_sub_Minf
  refine ⟨C, max s₁ (S' + 1), fun s hs t => ?_⟩
  have hcont : Continuous (PAp Jbar β g ψ v (s, t)) :=
    H.PAp_contDiff.continuous.uncurry_left (s, t)
  have key : ∀ θ ∈ Icc (0 : ℝ) 1,
      ‖PAp Jbar β g ψ v (s, t) θ - Minf Jinf (t + (cshift κ).2)‖ ≤
        C * Real.exp (-(d0 b b' δ * s)) := by
    intro θ hθ
    have hsS : S' < s := by linarith [le_max_right s₁ (S' + 1)]
    rw [(hS' s hsS t θ hθ).1]
    exact hC s (le_of_max_le_left hs) t ⟨θ, hθ⟩
  exact norm_integral_sub_const_le (F := ℂ →L[ℝ] ℂ) _ hcont _ _ key

/-- The projection `L ↦ [L(1, 0)]₂`. -/
def Mc : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.snd ℝ ℂ ℂ).comp (ContinuousLinearMap.apply ℝ (ℂ × ℂ) ((1 : ℂ), (0 : ℂ)))

lemma Minf_eq_Mc (τ : ℝ) : Minf Jinf τ = Mc.comp (Kd Jinf τ) := rfl

/-- `q ↦ (q.2, 0)`. -/
def Lsh : ℝ × ℝ →L[ℝ] ℝ × ℂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0

lemma bdH_Minf_shift (hJi : ContDiffOn ℝ ∞ Jinf (univ ×ˢ ball (0 : ℂ) ρ))
    (hper : ∀ (t : ℝ) (w : ℂ), Jinf (t + 1, w) = Jinf (t, w)) (hρ : 0 < ρ) (c : ℝ) :
    BdH (fun p : ℝ × ℝ => Minf Jinf (p.2 + c)) := by
  have hΦ : ContDiffOn ℝ ∞ (fun x => Mc.comp (PhiJ Jinf x)) (univ ×ˢ ball (0 : ℂ) ρ) :=
    contDiffOn_const.clm_comp (PhiJ_contDiffOn hJi)
  have hper' : ∀ τ w, Mc.comp (PhiJ Jinf (τ + 1, w)) = Mc.comp (PhiJ Jinf (τ, w)) :=
    fun τ w => by rw [PhiJ_per hper]
  have hX : ∀ _ : Unit, ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => Lsh q + ((c, 0) : ℝ × ℂ))
      (Ioi 0 ×ˢ univ) := fun _ => (Lsh.contDiff.add contDiff_const).contDiffOn
  have hXV : ∀ _ : Unit, ∀ s > (0 : ℝ), ∀ t : ℝ,
      Lsh (s, t) + ((c, 0) : ℝ × ℂ) ∈ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ :=
    fun _ s _ t => ⟨mem_univ _, by simp [Lsh, hρ]⟩
  have hF := bdF_comp (ι := Unit) (fun x => Mc.comp (PhiJ Jinf x)) _ (hO2 ρ) hΦ
    (fun _ q => Lsh q + ((c, 0) : ℝ × ℂ)) 0 hX hXV (fun n => by
      obtain ⟨CK, hCK⟩ := per_bound (fun x => Mc.comp (PhiJ Jinf x)) hρ hΦ hper' n
      refine ⟨CK, ‖Lsh‖, 1, fun _ s hs t => ⟨fun i hi => ?_, fun i hi1 _ =>
        norm_iteratedFDeriv_affine_le Lsh _ _ hi1⟩⟩
      have hpt : Lsh (s, t) + ((c, 0) : ℝ × ℂ) = (t + c, 0) := by simp [Lsh]
      rw [hpt]
      exact hCK _ 0 (by simp) i hi)
  have e : (fun p : ℝ × ℝ => Minf Jinf (p.2 + c)) =
      fun q => Mc.comp (PhiJ Jinf (Lsh q + ((c, 0) : ℝ × ℂ))) := by
    funext q
    rw [Minf_eq_Mc, Kd_eq_PhiJ hJi hρ]
    congr 2
    simp [Lsh]
  rw [e]
  exact hF.bdH ()

/-- The `KA`-term converges to `M∞(t + θ₀)` in `C^∞`, exponentially. -/
theorem EHyp.XA_decay (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) :
    ∀ d < d0 b b' δ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      (∫ θ in (0 : ℝ)..1, PAp Jbar β g ψ v p θ) - Minf Jinf (p.2 + (cshift κ).2)) d := by
  obtain ⟨-, -, -, hJi, hper, -, -, -⟩ := H.hT
  obtain ⟨C, s₁, hC⟩ := H.XA_c0
  exact expDecay_of_bdH (bdH_sub H.bdH_XA (bdH_Minf_shift hJi hper H.hρ _))
    (fun s hs t => hC s hs t) H.d0_pos

end

end FiniteEnergyPlane.B3E

/-! B3E layer S4: the coefficient `Tf` converges to `T∞(t + θ₀)` exponentially in `C^∞`. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

variable {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
  {Sinf : ℝ → Mat 1} {β : ContDiffBump (0 : ℂ)} {g ψ v : ℂ → ℂ} {r₁ δ : ℝ} {κ : ℂ} {b' : ℝ}
  {E : ℝ × ℝ → ℝ × ℝ} {S : ℝ}

/-- Composition of real-linear maps of `ℂ`, as a bilinear map. -/
def Bc : (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) := compL ℝ ℂ ℂ ℂ

lemma Bc_apply (A B : ℂ →L[ℝ] ℂ) : Bc A B = A.comp B := rfl

/-- `K ↦ y ↦ (u ↦ K u y)`. -/
def Bap : (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) →L[ℝ] ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  ((compL ℝ ℂ (ℂ →L[ℝ] ℂ) ℂ).comp (ContinuousLinearMap.apply ℝ ℂ)).flip

lemma Bap_apply (K : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (y : ℂ) :
    Bap K y = (ContinuousLinearMap.apply ℝ ℂ y).comp K := rfl

lemma smul_eq_mulL_comp (c : ℂ) (T : ℂ →L[ℝ] ℂ) : c • T = Bc (mulL c) T := by
  ext1 u; simp [Bc_apply]

/-- The `KA`-coefficient along the end. -/
def KAp (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (β : ContDiffBump (0 : ℂ)) (g ψ v : ℂ → ℂ)
    (p : ℝ × ℝ) : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  KA Jbar β g (ψ (cylInf p.1 p.2), hd g ψ v (cylInf p.1 p.2))

/-- The `KB`-coefficient along the end. -/
def KBp (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (β : ContDiffBump (0 : ℂ)) (g ψ v : ℂ → ℂ)
    (p : ℝ × ℝ) : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  KB Jbar β g (ψ (cylInf p.1 p.2), hd g ψ v (cylInf p.1 p.2))

lemma KBp_eq (p : ℝ × ℝ) : KBp Jbar β g ψ v p = ∫ θ in (0 : ℝ)..1, PBp Jbar β g ψ v p θ := rfl

lemma EHyp.XA_eq (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S) (p : ℝ × ℝ) :
    (ContinuousLinearMap.apply ℝ ℂ (fderiv ℝ ψ (cylInf p.1 p.2) (lam p.1 p.2))).comp
      (KAp Jbar β g ψ v p) = ∫ θ in (0 : ℝ)..1, PAp Jbar β g ψ v p θ := by
  have hA := (Afun_Bfun_contDiff H.hJ H.hrOut H.hg).1
  have hAx : ContDiff ℝ ∞ (fun a => Afun Jbar β g (ψ (cylInf p.1 p.2), a)) :=
    hA.comp (contDiff_const.prodMk contDiff_id)
  have hF : Continuous (fun θ : ℝ =>
      fderiv ℝ (fun a => Afun Jbar β g (ψ (cylInf p.1 p.2), a))
        (θ • hd g ψ v (cylInf p.1 p.2))) :=
    (hAx.continuous_fderiv (by simp)).comp (continuous_id.smul continuous_const)
  have hP : Continuous (PAp Jbar β g ψ v p) := H.PAp_contDiff.continuous.uncurry_left p
  ext1 u
  rw [ContinuousLinearMap.intervalIntegral_apply (hP.intervalIntegrable _ _)]
  simp only [comp_apply, ContinuousLinearMap.apply_apply, KAp, KA]
  rw [ContinuousLinearMap.intervalIntegral_apply (hF.intervalIntegrable _ _),
    ContinuousLinearMap.intervalIntegral_apply
      ((hF.clm_apply continuous_const).intervalIntegrable _ _)]
  rfl

/-- `Lmap` written through the end coefficients. -/
lemma EHyp.Lmap_eq (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S)
    (hP : ContDiff ℝ ∞ (Pf Jbar β g ψ)) (hhd : ContDiff ℝ ∞ (hd g ψ v)) (p : ℝ × ℝ) :
    Lmap Jbar β g ψ v (cylInf p.1 p.2) (c2 p) =
      fderiv ℝ (fun q : ℝ × ℝ => Pf Jbar β g ψ (cylInf q.1 q.2)) p ((0 : ℝ), (1 : ℝ)) -
        Bc (mulL Complex.I)
          (fderiv ℝ (fun q : ℝ × ℝ => Pf Jbar β g ψ (cylInf q.1 q.2)) p ((1 : ℝ), (0 : ℝ))) +
        Bc (Pf Jbar β g ψ (cylInf p.1 p.2)) (∫ θ in (0 : ℝ)..1, PAp Jbar β g ψ v p θ) +
        Bc (Pf Jbar β g ψ (cylInf p.1 p.2))
          (Bap (KBp Jbar β g ψ v p)
            (fderiv ℝ (fun q : ℝ × ℝ => hd g ψ v (cylInf q.1 q.2)) p ((1 : ℝ), (0 : ℝ)))) := by
  rw [(dPf_eq hP p).1, (dPf_eq hP p).2, dhd_eq hhd p, ← H.XA_eq p, ← smul_eq_mulL_comp,
    Bap_apply, Bc_apply, Bc_apply]
  rfl

lemma Bc_sub_id (A X : ℂ →L[ℝ] ℂ) :
    Bc A X = Bc (A - ContinuousLinearMap.id ℝ ℂ) X + X := by
  rw [Bc_apply, Bc_apply, sub_comp, id_comp, sub_add_cancel]

theorem EHyp.Lmap_decay (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S)
    (hP : ContDiff ℝ ∞ (Pf Jbar β g ψ)) (hhd : ContDiff ℝ ∞ (hd g ψ v)) {d : ℝ} (hd0 : 0 < d)
    (hd : d < d0 b b' δ) :
    ExpDecayCInfty (fun p : ℝ × ℝ =>
      Lmap Jbar β g ψ v (cylInf p.1 p.2) (c2 p) - Minf Jinf (p.2 + (cshift κ).2)) d := by
  have hdδ : d < -δ := hd.trans_le d0_le_δ
  have h01 := dPf_decay H.toAHyp hd0 hdδ ((0 : ℝ), (1 : ℝ))
  have h10 := expDecay_clm (Bc (mulL Complex.I)) (dPf_decay H.toAHyp hd0 hdδ ((1 : ℝ), (0 : ℝ)))
  have hPf := H.Pf_decay hd0 hdδ
  have hXA := expDecay_bilin Bc hPf H.bdH_XA
  have hXM := H.XA_decay d hd
  have hdh := expDecayCInfty_mono (dhd_decay H.toAHyp H.hvas) (hdδ.le)
  have hKB : BdH (KBp Jbar β g ψ v) := H.bdH_XB
  have hY := expDecay_bilin' Bap hKB hdh
  have hPY := expDecay_bilin Bc hPf (bdH_of_expDecay hd0.le hY)
  have hsum := expDecay_add (expDecay_add (expDecay_add (expDecay_add
    (expDecay_sub h01 h10) hXA) hXM) hPY) hY
  refine expDecayCInfty_congr (s₀ := 0) hsum fun s _ t => ?_
  rw [H.Lmap_eq hP hhd (s, t), Bc_sub_id (Pf Jbar β g ψ (cylInf (s, t).1 (s, t).2))
      (∫ θ in (0 : ℝ)..1, PAp Jbar β g ψ v (s, t) θ),
    Bc_sub_id (Pf Jbar β g ψ (cylInf (s, t).1 (s, t).2))]
  abel

lemma Tf_eq_Bc (p : ℝ × ℝ) : Tf Jbar β g ψ v p =
    Bc (mulL (-Complex.I)) (Bc (Lmap Jbar β g ψ v (cylInf p.1 p.2) (c2 p))
      (qinvL (cc Jbar β g ψ (cylInf p.1 p.2)))) := by
  rw [Tf, smul_eq_mulL_comp]
  rfl

theorem EHyp.Tf_decay (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S)
    (hP : ContDiff ℝ ∞ (Pf Jbar β g ψ)) (hhd : ContDiff ℝ ∞ (hd g ψ v)) {d : ℝ} (hd0 : 0 < d)
    (hd : d < d0 b b' δ) :
    ExpDecayCInfty (fun p : ℝ × ℝ =>
      Tf Jbar β g ψ v p - Tinf Jinf (p.2 + (cshift κ).2)) d := by
  obtain ⟨-, hsq, h0, hJi, hper, hdec, -, -⟩ := H.hT
  have hdδ : d < -δ := hd.trans_le d0_le_δ
  have hQd := H.qinv_decay hd0 hdδ
  have hQ : BdH (fun p : ℝ × ℝ => qinvL (cc Jbar β g ψ (cylInf p.1 p.2))) := by
    have := bdH_add (bdH_of_expDecay hd0.le hQd) (bdH_const (ContinuousLinearMap.id ℝ ℂ))
    simpa using this
  have h1 := expDecay_bilin Bc (H.Lmap_decay hP hhd hd0 hd) hQ
  have h2 := expDecay_bilin' Bc (bdH_Minf_shift hJi hper H.hρ (cshift κ).2) hQd
  have h3 := expDecay_clm (Bc (mulL (-Complex.I))) (expDecay_add h1 h2)
  refine expDecayCInfty_congr (s₀ := 0) h3 fun s _ t => ?_
  rw [Tf_eq_Bc, Tinf_eq H.hρ H.hb hJi h0 hsq hdec, smul_eq_mulL_comp]
  simp only [Bc_apply, sub_comp, comp_sub, comp_id, comp_add]
  abel

lemma Sinf_eq (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf) (τ : ℝ) :
    Sinf τ = cMat (Tinf Jinf τ) := by
  obtain ⟨-, -, -, -, -, -, -, hS⟩ := hT
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro a
  apply vecToC_injective
  rw [hS τ a, vecToC_cMat]
  rfl

/-- The coefficient matrix is exponentially asymptotic to the shifted limit loop. -/
theorem EHyp.Sf_asymptotic (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S)
    (hP : ContDiff ℝ ∞ (Pf Jbar β g ψ)) (hhd : ContDiff ℝ ∞ (hd g ψ v)) {d : ℝ} (hd0 : 0 < d)
    (hd : d < d0 b b' δ) :
    IsExpAsymptoticTo (Sf Jbar β g ψ v) (fun t => Sinf (t + Complex.arg κ / (2 * π))) d := by
  intro i j
  have h := expDecay_clm (entC i j) (H.Tf_decay hP hhd hd0 hd)
  refine expDecayCInfty_congr (s₀ := 0) h fun s _ t => ?_
  rw [map_sub, entC_apply, entC_apply]
  show Sf Jbar β g ψ v (s, t) i j - Sinf (t + Complex.arg κ / (2 * π)) i j = _
  rw [Sinf_eq H.hT]
  rfl

end

end FiniteEnergyPlane.B3E

/-! B3E: growth bound and assembly. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

lemma norm_cyl (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- A continuous map bounded by `C e^{δ s}` far out on the end is so bounded on all of `s > 0`. -/
lemma growth_of (ζ : ℂ → ℂ) (hζ : Continuous ζ) {δ : ℝ} (hδ : δ < 0) {C₁ s₁ : ℝ}
    (h : ∀ s ≥ s₁, ∀ t : ℝ, ‖ζ (cylInf s t)‖ ≤ C₁ * Real.exp (δ * s)) :
    ∃ C : ℝ, ∀ s > 0, ∀ t : ℝ, ‖ζ (cylInf s t)‖ ≤ C * Real.exp (δ * s) := by
  set s₂ := max s₁ 0
  obtain ⟨z₀, -, hz₀⟩ := (isCompact_closedBall (0 : ℂ) (Real.exp (2 * π * s₂))).exists_isMaxOn
    (nonempty_closedBall.2 (Real.exp_pos _).le) hζ.norm.continuousOn
  set M := ‖ζ z₀‖
  refine ⟨max C₁ (M * Real.exp (-(δ * s₂))), fun s hs t => ?_⟩
  by_cases h1 : s₁ ≤ s
  · exact (h s h1 t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have hs2 : s ≤ s₂ := (le_of_not_ge h1).trans (le_max_left _ _)
    have hmem : cylInf s t ∈ closedBall (0 : ℂ) (Real.exp (2 * π * s₂)) := by
      rw [mem_closedBall_zero_iff, norm_cyl]
      exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    have hM : ‖ζ (cylInf s t)‖ ≤ M := hz₀ hmem
    have he : 1 ≤ Real.exp (-(δ * s₂)) * Real.exp (δ * s) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    calc ‖ζ (cylInf s t)‖ ≤ M := hM
      _ ≤ M * (Real.exp (-(δ * s₂)) * Real.exp (δ * s)) :=
          le_mul_of_one_le_right (norm_nonneg _) he
      _ = M * Real.exp (-(δ * s₂)) * Real.exp (δ * s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

variable {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
  {Sinf : ℝ → Mat 1} {β : ContDiffBump (0 : ℂ)} {g ψ v : ℂ → ℂ} {r₁ δ : ℝ} {κ : ℂ} {b' : ℝ}
  {E : ℝ × ℝ → ℝ × ℝ} {S : ℝ}

theorem EHyp.wf_growth (H : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S)
    (hζ : Continuous (ζf Jbar β g ψ v)) :
    ∃ C : ℝ, ∀ s > 0, ∀ t : ℝ, ‖wf Jbar β g ψ v (s, t)‖ ≤ C * Real.exp (δ * s) := by
  have hdδ : -δ / 2 < -δ := by linarith [H.hδ]
  have hd0 : 0 < -δ / 2 := by linarith [H.hδ]
  obtain ⟨CP, sP, hCP0, hCP⟩ := ExpDecayCInfty.c0 (H.Pf_decay hd0 hdδ)
  obtain ⟨Ch, sh, hCh0, hCh⟩ := ExpDecayCInfty.c0 (hd_decay H.toAHyp H.hvas)
  have hfar : ∀ s ≥ max (max sP sh) 0, ∀ t : ℝ,
      ‖ζf Jbar β g ψ v (cylInf s t)‖ ≤ ((CP + 1) * Ch) * Real.exp (δ * s) := by
    intro s hs t
    have hsP : sP ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
    have hsh : sh ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
    have hs0 : 0 ≤ s := le_trans (le_max_right _ _) hs
    have h1 : ‖Pf Jbar β g ψ (cylInf s t)‖ ≤ CP + 1 := by
      have := hCP s hsP t
      have hle : Real.exp (-(-δ / 2 * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      calc ‖Pf Jbar β g ψ (cylInf s t)‖
          = ‖(Pf Jbar β g ψ (cylInf s t) - ContinuousLinearMap.id ℝ ℂ) +
              ContinuousLinearMap.id ℝ ℂ‖ := by rw [sub_add_cancel]
        _ ≤ ‖Pf Jbar β g ψ (cylInf s t) - ContinuousLinearMap.id ℝ ℂ‖ +
              ‖ContinuousLinearMap.id ℝ ℂ‖ := norm_add_le _ _
        _ ≤ CP * 1 + 1 := add_le_add (this.trans (mul_le_mul_of_nonneg_left hle hCP0))
              ContinuousLinearMap.norm_id_le
        _ = CP + 1 := by ring
    have h2 : ‖hd g ψ v (cylInf s t)‖ ≤ Ch * Real.exp (δ * s) := by
      have := hCh s hsh t
      simpa [neg_mul, neg_neg] using this
    calc ‖ζf Jbar β g ψ v (cylInf s t)‖
        ≤ ‖Pf Jbar β g ψ (cylInf s t)‖ * ‖hd g ψ v (cylInf s t)‖ := le_opNorm _ _
      _ ≤ (CP + 1) * (Ch * Real.exp (δ * s)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  obtain ⟨C, hC⟩ := growth_of _ hζ H.hδ hfar
  refine ⟨C, fun s hs t => ?_⟩
  rw [wf, norm_cToVec]
  exact hC s hs t

/-- The B3E assertion. -/
theorem exists_halfCyl_solution (ρ b : ℝ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0)
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgρ : ∀ x, g x ∈ ball (0 : ℂ) ρ)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1)
    (hgas : ExpDecayCInfty (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) (-δ))
    (ψ v : ℂ → ℂ) (κ : ℂ) (b' : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v) (hvρ : ∀ z, v z ∈ ball (0 : ℂ) ρ)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z))
    (hκ : κ ≠ 0) (hb' : 0 < b')
    (hψas : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b')
    (hvas : ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ)) :
    ∃ (P : ℂ → ℂ →L[ℝ] ℂ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1)
      (w : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (d C : ℝ),
      (∀ z, Function.Injective (P z)) ∧
      ContDiff ℝ ∞ (fun z => P z (v z - g (ψ z))) ∧
      (∀ z₀ : ℂ, ∃ r > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ r,
        ‖fderiv ℝ (fun y => P y (v y - g (ψ y))) z 1 +
            Complex.I * fderiv ℝ (fun y => P y (v y - g (ψ y))) z Complex.I‖ ≤
          M * ‖P z (v z - g (ψ z))‖) ∧
      (∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) ∧
      (∀ s t : ℝ, S (s, t + 1) = S (s, t)) ∧
      0 < d ∧ IsExpAsymptoticTo S (fun t => Sinf (t + Complex.arg κ / (2 * π))) d ∧
      IsHalfCylSolution S w ∧
      (∀ s > 0, ∀ t : ℝ, vecToC (w (s, t)) = P (cylInf s t) (v (cylInf s t) - g (ψ (cylInf s t)))) ∧
      ∀ s > 0, ∀ t : ℝ, ‖w (s, t)‖ ≤ C * Real.exp (δ * s) := by
  -- a common radius `r₁ < ρ` bounding `g` and `v`
  obtain ⟨rg, hrg0, hrgρ, hrg⟩ := exists_norm_le_of_expDecay g hg.continuous ρ hgρ δ hδ hgas
  obtain ⟨rv, hrv0, hrvρ, hrv⟩ := exists_norm_le_of_expDecay v hv.continuous ρ hvρ δ hδ hvas
  set r₁ := max rg rv with hr₁
  have hr₁0 : 0 ≤ r₁ := le_max_of_le_left hrg0
  have hr₁ρ : r₁ < ρ := max_lt hrgρ hrvρ
  have hgr : ∀ x, ‖g x‖ ≤ r₁ := fun x => (hrg x).trans (le_max_left _ _)
  have hvr : ∀ z, ‖v z‖ ≤ r₁ := fun z => (hrv z).trans (le_max_right _ _)
  have hρ : 0 < ρ := lt_of_le_of_lt hr₁0 hr₁ρ
  -- a bump with `r₁ < rIn < rOut ≤ ρ`
  let β : ContDiffBump (0 : ℂ) :=
    ⟨r₁ + (ρ - r₁) / 3, r₁ + 2 * (ρ - r₁) / 3, by linarith, by linarith⟩
  have hβIn : r₁ < β.rIn := by show r₁ < r₁ + (ρ - r₁) / 3; linarith
  have hβOut : β.rOut ≤ ρ := by show r₁ + 2 * (ρ - r₁) / 3 ≤ ρ; linarith
  have HP : Hyp Jbar β g ψ v ρ r₁ :=
    { hJ := hT.1, hsq := hT.2.1, hrIn := hβIn.le, hrOut := hβOut, hr₁ := hr₁ρ, hg := hg,
      hψ := hψ, hv := hv, hgr := hgr, hvr := hvr, hgJ := hgJ, hhol := hhol }
  have HA : AHyp ρ b Jbar Jinf Sinf β g ψ r₁ δ κ b' :=
    { hρ := hρ, hb := hb, hT := hT, hr₁ := hr₁ρ, hβ := hβIn.le, hgr := hgr, hg := hg,
      hδ := hδ, hgas := hgas, hκ := hκ, hb' := hb', hψas := hψas }
  obtain ⟨E, S₀, hL⟩ := HA.exists_LCData
  have HE : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S₀ :=
    ⟨HA, hψ, hv, hvr, hvas, hβIn, hβOut, hL⟩
  obtain ⟨C, hC⟩ := HE.wf_growth HP.ζf_contDiff.continuous
  have hd0 : 0 < d0 b b' δ / 2 := half_pos HE.d0_pos
  refine ⟨Pf Jbar β g ψ, Sf Jbar β g ψ v, wf Jbar β g ψ v, d0 b b' δ / 2, C,
    fun z => qL_injective _ (HP.cc_im z), HP.ζf_contDiff, HP.local_bound,
    HP.Sf_contDiff, Sf_per, hd0,
    HE.Sf_asymptotic HP.Pf_contDiff HP.hd_contDiff hd0 (half_lt_self HE.d0_pos),
    ⟨HP.wf_contDiff.contDiffOn, wf_per, fun s _ t => HP.crOp_eq_zero (s, t)⟩,
    fun s _ t => vecToC_wf s t, hC⟩

end

end FiniteEnergyPlane.B3E

/-! B3E child A: packaging of the asymptotics of the coefficient matrix and the growth bound. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

lemma Pf_contDiff_of {ρ r₁ : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {β : ContDiffBump (0 : ℂ)}
    {g ψ : ℂ → ℂ} (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hsq : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (hrIn : r₁ ≤ β.rIn) (hrOut : β.rOut ≤ ρ) (hr₁ : r₁ < ρ) (hg : ContDiff ℝ ∞ g)
    (hψ : ContDiff ℝ ∞ ψ) (hgr : ∀ x, ‖g x‖ ≤ r₁)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1) :
    ContDiff ℝ ∞ (Pf Jbar β g ψ) := by
  have hc : ContDiff ℝ ∞ (cc Jbar β g ψ) :=
    (((Afun_Bfun_contDiff hJ hrOut hg).2.comp (contDiff_id.prodMk contDiff_const)).comp
      hψ).clm_apply contDiff_const
  have him : ∀ z, (cc Jbar β g ψ z).im ≠ 0 := fun z =>
    im_ne_zero_of_sq _ (C0_sq hrIn hgr hr₁ hsq hgJ (ψ z))
  have hinv : ContDiff ℝ ∞ (fun z => ((cc Jbar β g ψ z).im)⁻¹) :=
    (Complex.imCLM.contDiff.comp hc).inv him
  have hW : ContDiff ℝ ∞ (fun z => (Complex.I - ((cc Jbar β g ψ z).re : ℂ)) *
      (((cc Jbar β g ψ z).im⁻¹ : ℝ) : ℂ)) :=
    (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hc))).mul
      (Complex.ofRealCLM.contDiff.comp hinv)
  have : Pf Jbar β g ψ = fun z => Complex.reCLM.smulRight (1 : ℂ) +
      Complex.imCLM.smulRight ((Complex.I - ((cc Jbar β g ψ z).re : ℂ)) *
        (((cc Jbar β g ψ z).im⁻¹ : ℝ) : ℂ)) := by
    funext z; exact qL_eq _
  rw [this]
  exact contDiff_const.add (contDiff_const.smulRight hW)

theorem isExpAsymptoticTo_Sf_aux (ρ b : ℝ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0) (β : ContDiffBump (0 : ℂ)) (r₁ : ℝ) (hr₁ : r₁ < ρ)
    (hrIn : r₁ < β.rIn) (hrOut : β.rOut ≤ ρ)
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgr : ∀ x, ‖g x‖ ≤ r₁)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1)
    (hgas : ExpDecayCInfty (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) (-δ))
    (ψ v : ℂ → ℂ) (κ : ℂ) (b' : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v) (hvr : ∀ z, ‖v z‖ ≤ r₁)
    (hκ : κ ≠ 0) (hb' : 0 < b')
    (hψas : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b')
    (hvas : ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ)) :
    (∀ d : ℝ, 0 < d → d < min (min b b') (-δ) →
      IsExpAsymptoticTo (Sf Jbar β g ψ v) (fun t => Sinf (t + Complex.arg κ / (2 * π))) d) ∧
      ∃ C : ℝ, ∀ s > 0, ∀ t : ℝ, ‖wf Jbar β g ψ v (s, t)‖ ≤ C * Real.exp (δ * s) := by
  have hρ : 0 < ρ := lt_of_le_of_lt ((norm_nonneg _).trans (hgr 0)) hr₁
  have HA : AHyp ρ b Jbar Jinf Sinf β g ψ r₁ δ κ b' :=
    { hρ := hρ, hb := hb, hT := hT, hr₁ := hr₁, hβ := hrIn.le, hgr := hgr, hg := hg,
      hδ := hδ, hgas := hgas, hκ := hκ, hb' := hb', hψas := hψas }
  obtain ⟨E, S₀, hL⟩ := HA.exists_LCData
  have HE : EHyp ρ b Jbar Jinf Sinf β g ψ v r₁ δ κ b' E S₀ :=
    ⟨HA, hψ, hv, hvr, hvas, hrIn, hrOut, hL⟩
  have hP : ContDiff ℝ ∞ (Pf Jbar β g ψ) :=
    Pf_contDiff_of hT.1 hT.2.1 hrIn.le hrOut hr₁ hg hψ hgr hgJ
  have hhd : ContDiff ℝ ∞ (hd g ψ v) := hv.sub (hg.comp hψ)
  have hζ : Continuous (ζf Jbar β g ψ v) := (hP.clm_apply hhd).continuous
  exact ⟨fun d hd0 hd => HE.Sf_asymptotic hP hhd hd0 hd, HE.wf_growth hζ⟩

end

end FiniteEnergyPlane.B3E

open FiniteEnergyPlane FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (ρ b : ℝ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0) (β : ContDiffBump (0 : ℂ)) (r₁ : ℝ) (hr₁ : r₁ < ρ)
    (hrIn : r₁ < β.rIn) (hrOut : β.rOut ≤ ρ)
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgr : ∀ x, ‖g x‖ ≤ r₁)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1)
    (hgas : ExpDecayCInfty (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) (-δ))
    (ψ v : ℂ → ℂ) (κ : ℂ) (b' : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v) (hvr : ∀ z, ‖v z‖ ≤ r₁)
    (hκ : κ ≠ 0) (hb' : 0 < b')
    (hψas : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b')
    (hvas : ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ)) :
    (∀ d : ℝ, 0 < d → d < min (min b b') (-δ) →
      IsExpAsymptoticTo (Sf Jbar β g ψ v) (fun t => Sinf (t + Complex.arg κ / (2 * π))) d) ∧
      ∃ C : ℝ, ∀ s > 0, ∀ t : ℝ, ‖wf Jbar β g ψ v (s, t)‖ ≤ C * Real.exp (δ * s) :=
  FiniteEnergyPlane.B3E.isExpAsymptoticTo_Sf_aux ρ b hb Jbar Jinf Sinf hT δ hδ β r₁ hr₁ hrIn hrOut g hg hgr hgJ hgas ψ v κ b' hψ hv hvr hκ hb' hψas hvas
