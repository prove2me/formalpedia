-- Prove2me | solution 1 for FiniteEnergyPlane.GraphEnd.halfCyl_equation_of_graph
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T15:33:04.787194+00:00
-- url     : https://prove2.me/submissions/ec7065fb-f01a-4f64-90a4-c58676d796eb

import Definitions.Def_FiniteEnergyPlane_GraphEnd
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_comp_left
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_congr
import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_hadamard_integral_fderiv
import Definitions.Def_FiniteEnergyPlane_TubeFamily



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

/-! B3E child P: packaging of the end equation. -/

namespace FiniteEnergyPlane.B3E

open FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

theorem halfCyl_equation_of_graph_aux (ρ r₁ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hsq : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (β : ContDiffBump (0 : ℂ)) (hrIn : r₁ ≤ β.rIn) (hrOut : β.rOut ≤ ρ) (hr₁ : r₁ < ρ)
    (g ψ v : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v)
    (hgr : ∀ x, ‖g x‖ ≤ r₁) (hvr : ∀ z, ‖v z‖ ≤ r₁)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z)) :
    (∀ z, Function.Injective (Pf Jbar β g ψ z)) ∧
      ContDiff ℝ ∞ (ζf Jbar β g ψ v) ∧
      (∀ z₀ : ℂ, ∃ r > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ r,
        ‖fderiv ℝ (fun y => Pf Jbar β g ψ y (v y - g (ψ y))) z 1 +
            Complex.I * fderiv ℝ (fun y => Pf Jbar β g ψ y (v y - g (ψ y))) z Complex.I‖ ≤
          M * ‖Pf Jbar β g ψ z (v z - g (ψ z))‖) ∧
      (∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => Sf Jbar β g ψ v p i j)) ∧
      (∀ s t : ℝ, Sf Jbar β g ψ v (s, t + 1) = Sf Jbar β g ψ v (s, t)) ∧
      IsHalfCylSolution (Sf Jbar β g ψ v) (wf Jbar β g ψ v) ∧
      ∀ s t : ℝ, vecToC (wf Jbar β g ψ v (s, t)) = ζf Jbar β g ψ v (cylInf s t) := by
  have HP : Hyp Jbar β g ψ v ρ r₁ :=
    { hJ := hJ, hsq := hsq, hrIn := hrIn, hrOut := hrOut, hr₁ := hr₁, hg := hg, hψ := hψ,
      hv := hv, hgr := hgr, hvr := hvr, hgJ := hgJ, hhol := hhol }
  exact ⟨fun z => qL_injective _ (HP.cc_im z), HP.ζf_contDiff, HP.local_bound, HP.Sf_contDiff,
    Sf_per, ⟨HP.wf_contDiff.contDiffOn, wf_per, fun s _ t => HP.crOp_eq_zero (s, t)⟩,
    fun s t => vecToC_wf s t⟩

end

end FiniteEnergyPlane.B3E

open FiniteEnergyPlane FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (ρ r₁ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hsq : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (β : ContDiffBump (0 : ℂ)) (hrIn : r₁ ≤ β.rIn) (hrOut : β.rOut ≤ ρ) (hr₁ : r₁ < ρ)
    (g ψ v : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v)
    (hgr : ∀ x, ‖g x‖ ≤ r₁) (hvr : ∀ z, ‖v z‖ ≤ r₁)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z)) :
    (∀ z, Function.Injective (Pf Jbar β g ψ z)) ∧
      ContDiff ℝ ∞ (ζf Jbar β g ψ v) ∧
      (∀ z₀ : ℂ, ∃ r > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ r,
        ‖fderiv ℝ (fun y => Pf Jbar β g ψ y (v y - g (ψ y))) z 1 +
            Complex.I * fderiv ℝ (fun y => Pf Jbar β g ψ y (v y - g (ψ y))) z Complex.I‖ ≤
          M * ‖Pf Jbar β g ψ z (v z - g (ψ z))‖) ∧
      (∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => Sf Jbar β g ψ v p i j)) ∧
      (∀ s t : ℝ, Sf Jbar β g ψ v (s, t + 1) = Sf Jbar β g ψ v (s, t)) ∧
      IsHalfCylSolution (Sf Jbar β g ψ v) (wf Jbar β g ψ v) ∧
      ∀ s t : ℝ, vecToC (wf Jbar β g ψ v (s, t)) = ζf Jbar β g ψ v (cylInf s t) :=
  FiniteEnergyPlane.B3E.halfCyl_equation_of_graph_aux ρ r₁ Jbar hJ hsq β hrIn hrOut hr₁ g ψ v hg hψ hv hgr hvr hgJ hhol
