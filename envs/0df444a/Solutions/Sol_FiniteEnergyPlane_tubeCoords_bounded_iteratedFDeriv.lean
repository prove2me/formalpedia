-- Prove2me | solution 1 for FiniteEnergyPlane.tubeCoords_bounded_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T18:56:55.935172+00:00
-- url     : https://prove2.me/submissions/e387895a-dbd8-4393-be0c-d3934413c0ae

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Theorems.Thm_FiniteEnergyPlane_exists_cylInf_tubeMap_immersion_bounds
import Theorems.Thm_FiniteEnergyPlane_bounded_iteratedFDeriv_of_comp_immersion



/-!
# R′ helpers: elementary derivative bounds on the cylinder `ℝ × ℝ`

Bounds for maps with constant derivative, for smooth maps that are `1`-periodic in `t` (on strips
of bounded `s`), the collection of finitely many bounds into one, `cylInf` identities, and the
bounded derivatives of `(endA f, endW f)` coming from exponential asymptotics.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

namespace DGA3R

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

lemma norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

lemma cylInf_ne_zero (s t : ℝ) : cylInf s t ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_cylInf]; exact (Real.exp_pos _).ne'

lemma cylInf_add (a b c e : ℝ) : cylInf (a + c) (b + e) = cylInf a b * cylInf c e := by
  unfold cylInf ccwLoop
  rw [show 2 * π * (a + c) = 2 * π * a + 2 * π * c by ring, Real.exp_add,
    show 2 * π * (b + e) = 2 * π * b + 2 * π * e by ring]
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

lemma cylInf_re_im (w : ℂ) : cylInf (w.re / (2 * π)) (w.im / (2 * π)) = Complex.exp w := by
  unfold cylInf ccwLoop
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  rw [show 2 * π * (w.re / (2 * π)) = w.re by field_simp,
    show 2 * π * (w.im / (2 * π)) = w.im by field_simp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  exact Complex.re_add_im w

lemma cylInf_add_int (a b : ℝ) (n : ℤ) : cylInf a (b + n) = cylInf a b := by
  have h := cylInf_add a b 0 n
  rw [add_zero] at h
  rw [h]
  have h1 : cylInf 0 n = 1 := by
    unfold cylInf ccwLoop
    rw [mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul]
    rw [show (((2 * π * n : ℝ)) : ℂ) * Complex.I = n * (2 * π * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  rw [h1, mul_one]

lemma contDiff_cylInf : ContDiff ℝ ∞ (fun q : ℝ × ℝ => cylInf q.1 q.2) := by
  have e : (fun q : ℝ × ℝ => cylInf q.1 q.2) = fun q : ℝ × ℝ =>
      Complex.ofRealCLM (Real.exp (2 * π * q.1)) *
        Complex.exp (Complex.ofRealCLM (2 * π * q.2) * Complex.I) := rfl
  rw [e]
  refine (Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst))).mul ?_
  exact Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_snd)).mul contDiff_const)

/-- Derivatives of order `≥ 1` of a map with constant derivative. -/
lemma norm_iteratedFDeriv_le_of_hasFDerivAt_const {f : E → F} (L : E →L[ℝ] F)
    (hf : ∀ x, HasFDerivAt f L x) (k : ℕ) (hk : 1 ≤ k) (x : E) :
    ‖iteratedFDeriv ℝ k f x‖ ≤ ‖L‖ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv]
  have e : fderiv ℝ f = fun _ => L := funext fun x => (hf x).fderiv
  rw [e]
  rcases j with _ | j
  · simp
  · rw [iteratedFDeriv_const_of_ne (by omega)]; simp

/-- Equal functions on an open set have equal iterated derivatives there. -/
lemma iteratedFDeriv_eq_of_eqOn {f g : E → F} {U : Set E} (hU : IsOpen U) (h : EqOn f g U)
    {x : E} (hx : x ∈ U) (n : ℕ) : iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  rw [← iteratedFDerivWithin_of_isOpen n hU hx, ← iteratedFDerivWithin_of_isOpen n hU hx]
  exact iteratedFDerivWithin_congr h hx n

lemma periodic_int {G : ℝ × ℝ → F} (hper : ∀ q : ℝ × ℝ, G (q + (0, 1)) = G q) (n : ℤ)
    (q : ℝ × ℝ) : G (q + (0, (n : ℝ))) = G q := by
  induction n using Int.induction_on generalizing q with
  | zero => rw [Int.cast_zero, Prod.mk_zero_zero, add_zero]
  | succ n ih =>
    have e : q + (0, (((n : ℤ) + 1 : ℤ) : ℝ)) = (q + (0, (((n : ℤ) : ℤ) : ℝ))) + (0, 1) := by
      push_cast; ext <;> simp; ring
    rw [e, hper, ih]
  | pred n ih =>
    have e : (q + (0, ((-(n : ℤ) - 1 : ℤ) : ℝ))) + (0, 1) = q + (0, ((-(n : ℤ) : ℤ) : ℝ)) := by
      push_cast; ext <;> simp; ring
    rw [← ih q, ← e, hper]

/-- Smooth maps `1`-periodic in `t` have bounded derivatives on strips of bounded `s`. -/
lemma strip_bound {G : ℝ × ℝ → F} (hG : ContDiff ℝ ∞ G)
    (hper : ∀ q : ℝ × ℝ, G (q + (0, 1)) = G q) (lo hi : ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ a ∈ Icc lo hi, ∀ b : ℝ, ‖iteratedFDeriv ℝ k G (a, b)‖ ≤ C := by
  set K : Set (ℝ × ℝ) := Icc lo hi ×ˢ Icc (0 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (iteratedFDeriv ℝ k G) K :=
    (hG.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨C, fun a ha b => ?_⟩
  set v : ℝ × ℝ := (0, ((⌊b⌋ : ℤ) : ℝ)) with hv
  set x : ℝ × ℝ := (a, Int.fract b) with hx
  have hxK : x ∈ K := ⟨ha, ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩
  have hxv : x + v = (a, b) := by
    simp only [hx, hv, Prod.mk_add_mk, add_zero, Int.fract_add_floor]
  have hfun : (fun z => G (z + v)) = G := funext fun z => periodic_int hper _ z
  have e : iteratedFDeriv ℝ k G (a, b) = iteratedFDeriv ℝ k G x := by
    rw [← hxv, ← iteratedFDeriv_comp_add_right, hfun]
  rw [e]
  exact hC x hxK

/-- Finitely many strip bounds combine into one. -/
lemma strip_bound_le {G : ℝ × ℝ → F} {lo hi : ℝ}
    (h : ∀ k : ℕ, ∃ C : ℝ, ∀ a ∈ Icc lo hi, ∀ b : ℝ, ‖iteratedFDeriv ℝ k G (a, b)‖ ≤ C)
    (n : ℕ) : ∃ C : ℝ, ∀ i ≤ n, ∀ a ∈ Icc lo hi, ∀ b : ℝ, ‖iteratedFDeriv ℝ i G (a, b)‖ ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := h 0
    exact ⟨C, fun i hi a ha b => by
      obtain rfl : i = 0 := by omega
      exact hC a ha b⟩
  | succ n ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨C', hC'⟩ := h (n + 1)
    refine ⟨max C C', fun i hi a ha b => ?_⟩
    rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
    · exact (hC i (by omega) a ha b).trans (le_max_left _ _)
    · obtain rfl : i = n + 1 := by omega
      exact (hC' a ha b).trans (le_max_right _ _)

/-- Finitely many derivative bounds combine into bounds by powers `D ^ i` with `1 ≤ D`. -/
lemma pow_bounds {X : ℝ × ℝ → F}
    (h : ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m X (s, t)‖ ≤ C)
    (n : ℕ) : ∃ D s₁ : ℝ, 1 ≤ D ∧ ∀ i, 1 ≤ i → i ≤ n → ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ i X (s, t)‖ ≤ D ^ i := by
  induction n with
  | zero => exact ⟨1, 0, le_rfl, fun i h1 h2 => by omega⟩
  | succ n ih =>
    obtain ⟨D, s₁, hD1, hD⟩ := ih
    obtain ⟨C, s₂, hC⟩ := h (n + 1) (by omega)
    refine ⟨max D (max 1 C), max s₁ s₂, le_trans hD1 (le_max_left _ _), fun i h1 h2 s hs t => ?_⟩
    have hD0 : 0 ≤ D := by linarith
    have hs1 : s₁ ≤ s := le_trans (le_max_left _ _) hs
    have hs2 : s₂ ≤ s := le_trans (le_max_right _ _) hs
    have hM1 : 1 ≤ max D (max 1 C) := le_trans (le_max_left 1 C) (le_max_right _ _)
    rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
    · exact (hD i h1 (by omega) s hs1 t).trans
        (pow_le_pow_left₀ hD0 (le_max_left _ _) i)
    · obtain rfl : i = n + 1 := by omega
      calc ‖iteratedFDeriv ℝ (n + 1) X (s, t)‖ ≤ C := hC s hs2 t
        _ ≤ max D (max 1 C) := le_trans (le_max_right 1 C) (le_max_right _ _)
        _ ≤ max D (max 1 C) ^ (n + 1) := le_self_pow₀ hM1 (by omega)

lemma norm_sub_self_le {ψ : ℂ → ℂ} (hψ : Differentiable ℝ ψ)
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) (z : ℂ) :
    ‖ψ z - z‖ ≤ ‖ψ 0‖ + 1 / 2 * ‖z‖ := by
  set g : ℂ → ℂ := fun z => ψ z - z with hg
  have hgd : ∀ x, HasFDerivAt g (fderiv ℝ ψ x - ContinuousLinearMap.id ℝ ℂ) x := fun x =>
    (hψ x).hasFDerivAt.sub (hasFDerivAt_id x)
  have hb : ∀ x ∈ (univ : Set ℂ), ‖fderiv ℝ g x‖ ≤ 1 / 2 := fun x _ => by
    rw [(hgd x).fderiv]; exact hDψ x
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => (hgd x).differentiableAt) hb
    convex_univ (mem_univ (0 : ℂ)) (mem_univ z)
  simp only [hg, sub_zero] at h
  have := norm_sub_norm_le (ψ z - z) (ψ 0)
  linarith

/-- Bounded derivatives of order `≥ 1` of `(endA f, endW f)` from exponential asymptotics. -/
lemma endAW_bound (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
    (f : ℂ → V 1) (df cf bf : ℝ)
    (hfa : ExpDecayCInfty (fun p : ℝ × ℝ => endA H f cylInf p - P.T * p.1 - df) bf)
    (hfw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H f cylInf p - P.x (P.T * p.2 + cf)) bf)
    (hbf : 0 < bf) (m : ℕ) (hm : 1 ≤ m) :
    ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => (endA H f cylInf p, endW H f cylInf p)) (s, t)‖
        ≤ C := by
  obtain ⟨⟨sa, hsa⟩, hCa⟩ := hfa
  obtain ⟨⟨sw, hsw⟩, hCw⟩ := hfw
  obtain ⟨Ca, sa', hCa⟩ := hCa m
  obtain ⟨Cw, sw', hCw⟩ := hCw m
  set gA : ℝ × ℝ → ℝ := fun p => endA H f cylInf p - P.T * p.1 - df with hgA
  set gW : ℝ × ℝ → V 1 := fun p => endW H f cylInf p - P.x (P.T * p.2 + cf) with hgW
  set aff : ℝ × ℝ → ℝ := fun p => P.T * p.1 + df with haff
  set hx : ℝ × ℝ → V 1 := fun p => P.x (P.T * p.2 + cf) with hhx
  have hxs : ContDiff ℝ ∞ P.x := ReebOrbit.contDiff_x H hH P
  have hhxc : ContDiff ℝ ∞ hx :=
    hxs.comp ((contDiff_const.mul contDiff_snd).add contDiff_const)
  have haffd : ∀ p, HasFDerivAt aff (P.T • ContinuousLinearMap.fst ℝ ℝ ℝ) p := fun p =>
    ((hasFDerivAt_fst).const_smul P.T).add_const df
  have haffc : ContDiff ℝ ∞ aff := (contDiff_const.mul contDiff_fst).add contDiff_const
  -- bound for the periodic part
  have hper : ∀ q : ℝ × ℝ, hx (q + (0, 1)) = hx q := fun q => by
    simp only [hhx, Prod.fst_add, Prod.snd_add, add_zero]
    rw [show P.T * (q.2 + 1) + cf = P.T * q.2 + cf + P.T by ring, P.periodic]
  obtain ⟨Cx, hCx⟩ := strip_bound hhxc hper 0 0 m
  have hxb : ∀ s t : ℝ, ‖iteratedFDeriv ℝ m hx (s, t)‖ ≤ Cx := fun s t => by
    have hfun : (fun z => hx (z + (s, 0))) = hx := funext fun z => by
      simp only [hhx, Prod.snd_add, add_zero]
    have e : iteratedFDeriv ℝ m hx (s, t) = iteratedFDeriv ℝ m hx (0, t) := by
      have : ((0 : ℝ), t) + (s, 0) = (s, t) := by simp
      rw [← this, ← iteratedFDeriv_comp_add_right, hfun]
    rw [e]; exact hCx 0 ⟨le_rfl, le_rfl⟩ t
  refine ⟨max (|Ca| + ‖P.T • ContinuousLinearMap.fst ℝ ℝ ℝ‖) (|Cw| + Cx),
    max (max sa sw + 1) (max (max sa' sw') 0), fun s hs t => ?_⟩
  have hs1 : max sa sw + 1 ≤ s := le_trans (le_max_left _ _) hs
  have hs2 : max (max sa' sw') 0 ≤ s := le_trans (le_max_right _ _) hs
  have hs0 : 0 ≤ s := le_trans (le_max_right _ _) hs2
  have hsa' : sa' ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs2
  have hsw' : sw' ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs2
  have hmemA : (s, t) ∈ Ioi sa ×ˢ (univ : Set ℝ) :=
    ⟨by simp only [mem_Ioi]; linarith [le_max_left sa sw], trivial⟩
  have hmemW : (s, t) ∈ Ioi sw ×ˢ (univ : Set ℝ) :=
    ⟨by simp only [mem_Ioi]; linarith [le_max_right sa sw], trivial⟩
  have hgAc : ContDiffAt ℝ ∞ gA (s, t) :=
    hsa.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmemA)
  have hgWc : ContDiffAt ℝ ∞ gW (s, t) :=
    hsw.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmemW)
  have hexp : Real.exp (-(bf * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have e1 : (fun p : ℝ × ℝ => endA H f cylInf p) = gA + aff := funext fun p => by
    simp only [Pi.add_apply, hgA, haff]; ring
  have e2 : (fun p : ℝ × ℝ => endW H f cylInf p) = gW + hx := funext fun p => by
    simp only [Pi.add_apply, hgW, hhx]; abel
  have hAc : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => endA H f cylInf p) (s, t) := by
    rw [e1]; exact hgAc.add haffc.contDiffAt
  have hWc : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => endW H f cylInf p) (s, t) := by
    rw [e2]; exact hgWc.add hhxc.contDiffAt
  rw [iteratedFDeriv_prodMk hAc hWc (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)),
    ContinuousMultilinearMap.opNorm_prod]
  refine max_le_max ?_ ?_
  · rw [e1, iteratedFDeriv_add_apply (hgAc.of_le (by exact_mod_cast le_top))
      (haffc.contDiffAt.of_le (by exact_mod_cast le_top))]
    refine (norm_add_le _ _).trans (add_le_add ?_
      (norm_iteratedFDeriv_le_of_hasFDerivAt_const _ haffd m hm _))
    calc ‖iteratedFDeriv ℝ m gA (s, t)‖ ≤ Ca * Real.exp (-(bf * s)) := hCa s hsa' t
      _ ≤ |Ca| * Real.exp (-(bf * s)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ |Ca| * 1 := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
      _ = |Ca| := mul_one _
  · rw [e2, iteratedFDeriv_add_apply (hgWc.of_le (by exact_mod_cast le_top))
      (hhxc.contDiffAt.of_le (by exact_mod_cast le_top))]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hxb s t))
    calc ‖iteratedFDeriv ℝ m gW (s, t)‖ ≤ Cw * Real.exp (-(bf * s)) := hCw s hsw' t
      _ ≤ |Cw| * Real.exp (-(bf * s)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ |Cw| * 1 := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
      _ = |Cw| := mul_one _

end DGA3R

end FiniteEnergyPlane

/-!
# R′: bounded derivatives of the tube coordinates on the end

Lift `q = ψ(z)/z` (`z = cylInf s t`) by `L = log q` to `X(s, t) = (s + Re L/2π, t + Im L/2π, v z)`.
Then `Ξ ∘ X = (endA f, endW f)` on the end, where `Ξ` is the tube map in cylindrical coordinates
(T∞), so the immersion transfer (B) bounds the derivatives of `X`. Finally `q = cylInf ∘ Y` with
`Y = (Re L/2π, Im L/2π)`, and Faà di Bruno bounds `q`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real Nat

open DGA3R in
theorem tubeCoords_bounded_iteratedFDeriv_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (f : ℂ → V 1) (df cf bf : ℝ) (hbf : 0 < bf)
    (hfa : ExpDecayCInfty (fun p : ℝ × ℝ => endA H f cylInf p - P.T * p.1 - df) bf)
    (hfw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H f cylInf p - P.x (P.T * p.2 + cf)) bf)
    (ψ v : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v)
    (hf : ∀ z, f z = u (ψ z) + N (ψ z) (v z))
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2)
    (hv0 : Tendsto v (cocompact ℂ) (𝓝 0)) :
    ∀ m : ℕ, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2) (s, t)‖ ≤ C ∧
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (s, t)‖ ≤ C := by
  obtain ⟨r, hr, c, hc, s₀, -, hΞs, hΞb, hlow⟩ := exists_cylInf_tubeMap_immersion_bounds H hH J P
    u hu hu0 d b hb ha hw N hN hNinj M hM hNM
  set Ξ : ℝ × ℝ × ℂ → ℝ × V 1 := fun q : ℝ × ℝ × ℂ =>
    (aCoord H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2),
      proj H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2)) with hΞdef
  set Ω : Set (ℝ × ℝ × ℂ) := Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) r with hΩ
  have hΩo : IsOpen Ω := isOpen_Ioi.prod (isOpen_univ.prod isOpen_ball)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  -- a radius beyond which `‖v‖ < r`
  obtain ⟨Rv, hRv⟩ : ∃ Rv : ℝ, ∀ z : ℂ, Rv ≤ ‖z‖ → ‖v z‖ < r := by
    have h1 := hv0.eventually (ball_mem_nhds (0 : ℂ) hr)
    rw [← cobounded_eq_cocompact, ← comap_norm_atTop, Filter.eventually_comap,
      Filter.eventually_atTop] at h1
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, fun z hz => mem_ball_zero_iff.1 (ha ‖z‖ hz z rfl)⟩
  have hπ : 0 < 2 * π := by positivity
  set R₀ : ℝ := max Rv (4 * ‖ψ 0‖ + 1) with hR₀
  set lo : ℝ := Real.log (1 / 4) / (2 * π) with hlo
  set hi : ℝ := Real.log 2 / (2 * π) with hhi
  have hlo0 : lo ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (Real.log_nonpos (by norm_num) (by norm_num)) hπ.le
  set S : ℝ := max (max (s₀ - lo + 1) R₀) 0 with hS
  set Z : ℝ × ℝ → ℂ := fun p => cylInf p.1 p.2 with hZ
  set q : ℝ × ℝ → ℂ := fun p => ψ (Z p) * cylInf (-p.1) (-p.2) with hq
  set L : ℝ × ℝ → ℂ := fun p => Complex.log (q p) with hL
  set Y : ℝ × ℝ → ℝ × ℝ := fun p => ((L p).re / (2 * π), (L p).im / (2 * π)) with hY
  set X : ℝ × ℝ → ℝ × ℝ × ℂ := fun p => (p.1 + (Y p).1, p.2 + (Y p).2, v (Z p)) with hX
  set U : Set (ℝ × ℝ) := Ioi S ×ˢ (univ : Set ℝ) with hU
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  -- pointwise facts
  have hZinv : ∀ p : ℝ × ℝ, Z p * cylInf (-p.1) (-p.2) = 1 := fun p => by
    simp only [hZ]
    rw [← cylInf_add, add_neg_cancel, add_neg_cancel]
    simp [cylInf, ccwLoop]
  have hq_eq : ∀ p : ℝ × ℝ, q p = ψ (Z p) / Z p := fun p => by
    have hz : Z p ≠ 0 := cylInf_ne_zero _ _
    have e : cylInf (-p.1) (-p.2) = (Z p)⁻¹ := eq_inv_of_mul_eq_one_right (hZinv p)
    simp only [hq, e, div_eq_mul_inv]
  have hZn : ∀ p ∈ U, R₀ ≤ ‖Z p‖ := fun p hp => by
    have hs : S < p.1 := hp.1
    have h0 : 0 ≤ p.1 := le_trans (le_max_right _ _) hs.le
    have hR : R₀ ≤ p.1 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs.le
    simp only [hZ, norm_cylInf]
    have := Real.add_one_le_exp (2 * π * p.1)
    have h2 : p.1 ≤ 2 * π * p.1 := by nlinarith [Real.pi_gt_three]
    linarith
  have hq1 : ∀ p ∈ U, ‖q p - 1‖ ≤ 3 / 4 := fun p hp => by
    have hz : Z p ≠ 0 := cylInf_ne_zero _ _
    have hzpos : 0 < ‖Z p‖ := norm_pos_iff.2 hz
    have h4 : 4 * ‖ψ 0‖ + 1 ≤ ‖Z p‖ := le_trans (le_max_right _ _) (hZn p hp)
    have e : q p - 1 = (ψ (Z p) - Z p) / Z p := by rw [hq_eq]; field_simp
    rw [e, norm_div, div_le_iff₀ hzpos]
    have := norm_sub_self_le hψd hDψ (Z p)
    linarith
  have hqre : ∀ p ∈ U, 0 < (q p).re := fun p hp => by
    have h1 := Complex.abs_re_le_norm (q p - 1)
    have h2 := hq1 p hp
    rw [Complex.sub_re, Complex.one_re] at h1
    have := neg_abs_le ((q p).re - 1)
    linarith
  have hqn : ∀ p ∈ U, 1 / 4 ≤ ‖q p‖ ∧ ‖q p‖ ≤ 2 := fun p hp => by
    have h2 := hq1 p hp
    have a1 := norm_sub_norm_le (1 : ℂ) (q p)
    have a2 := norm_sub_norm_le (q p) 1
    rw [norm_sub_rev] at a1
    rw [norm_one] at a1 a2
    constructor <;> linarith
  have hq0 : ∀ p ∈ U, q p ≠ 0 := fun p hp h => by
    have := (hqn p hp).1; rw [h, norm_zero] at this; norm_num at this
  have hYre : ∀ p ∈ U, (Y p).1 ∈ Icc lo hi := fun p hp => by
    have hqp : 0 < ‖q p‖ := norm_pos_iff.2 (hq0 p hp)
    simp only [hY, hL, Complex.log_re]
    exact ⟨div_le_div_of_nonneg_right (Real.log_le_log (by norm_num) (hqn p hp).1) hπ.le,
      div_le_div_of_nonneg_right (Real.log_le_log hqp (hqn p hp).2) hπ.le⟩
  have hcylY : ∀ p ∈ U, cylInf (Y p).1 (Y p).2 = q p := fun p hp => by
    simp only [hY]; rw [cylInf_re_im, hL, Complex.exp_log (hq0 p hp)]
  have hcylX : ∀ p ∈ U, cylInf (X p).1 (X p).2.1 = ψ (Z p) := fun p hp => by
    simp only [hX]
    rw [cylInf_add, hcylY p hp]
    show Z p * (ψ (Z p) * cylInf (-p.1) (-p.2)) = ψ (Z p)
    rw [mul_left_comm, hZinv, mul_one]
  have hXΩ : ∀ p ∈ U, X p ∈ Ω := fun p hp => by
    have hs : S < p.1 := hp.1
    have h1 : s₀ - lo + 1 ≤ p.1 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs.le
    have h2 := (hYre p hp).1
    refine ⟨?_, mem_univ _, mem_ball_zero_iff.2 (hRv _ (le_trans (le_max_left _ _) (hZn p hp)))⟩
    show s₀ < p.1 + (Y p).1
    linarith
  -- smoothness
  have hZc : ContDiff ℝ ∞ Z := contDiff_cylInf
  have hqc : ContDiff ℝ ∞ q :=
    (hψ.comp hZc).mul (contDiff_cylInf.comp (contDiff_fst.neg.prodMk contDiff_snd.neg))
  have hLc : ∀ p ∈ U, ContDiffAt ℝ ∞ L p := fun p hp =>
    ((Complex.contDiffAt_log (Complex.mem_slitPlane_iff.2 (Or.inl (hqre p hp)))).restrict_scalars
      ℝ).comp p hqc.contDiffAt
  have hYc : ∀ p ∈ U, ContDiffAt ℝ ∞ Y p := fun p hp =>
    ((Complex.reCLM.contDiff.contDiffAt.comp p (hLc p hp)).div_const _).prodMk
      ((Complex.imCLM.contDiff.contDiffAt.comp p (hLc p hp)).div_const _)
  have hXc : ∀ p ∈ U, ContDiffAt ℝ ∞ X p := fun p hp =>
    (contDiffAt_fst.add (hYc p hp).fst).prodMk
      ((contDiffAt_snd.add (hYc p hp).snd).prodMk (hv.comp hZc).contDiffAt)
  have hXon : ContDiffOn ℝ ∞ X U := fun p hp => (hXc p hp).contDiffWithinAt
  have hYon : ContDiffOn ℝ ∞ Y U := fun p hp => (hYc p hp).contDiffWithinAt
  -- the composite
  have hΞX : EqOn (fun p => Ξ (X p))
      (fun p : ℝ × ℝ => (endA H f cylInf p, endW H f cylInf p)) U := fun p hp => by
    show (aCoord H (u (cylInf (X p).1 (X p).2.1) + N (cylInf (X p).1 (X p).2.1) (X p).2.2),
      proj H (u (cylInf (X p).1 (X p).2.1) + N (cylInf (X p).1 (X p).2.1) (X p).2.2)) =
      (aCoord H (f (cylInf p.1 p.2)), proj H (f (cylInf p.1 p.2)))
    rw [hcylX p hp, show (X p).2.2 = v (Z p) from rfl, ← hf]
  have memU : ∀ s t : ℝ, S + 1 ≤ s → (s, t) ∈ U := fun s t hs =>
    ⟨show S < s by linarith, mem_univ _⟩
  -- derivative bounds of `X`
  have hB := bounded_iteratedFDeriv_of_comp_immersion Ξ Ω hΩo hΞs X S hXon
    (fun s hs t => hXΩ (s, t) ⟨hs, mem_univ _⟩)
    (fun m hm => by
      obtain ⟨C, s₁, h⟩ := hΞb m hm
      refine ⟨C, max (S + 1) (s₁ - lo), fun s hs t => ?_⟩
      have hp := memU s t (le_trans (le_max_left _ _) hs)
      refine h (X (s, t)) (hXΩ _ hp) ?_
      have := (hYre _ hp).1
      have := le_trans (le_max_right _ _) hs
      show s₁ ≤ s + (Y (s, t)).1
      linarith)
    c hc (fun s hs t h => hlow _ (hXΩ (s, t) ⟨hs, mem_univ _⟩) h)
    (fun m hm => by
      obtain ⟨C, s₁, h⟩ := endAW_bound H hH P f df cf bf hfa hfw hbf m hm
      refine ⟨C, max (S + 1) s₁, fun s hs t => ?_⟩
      have hp := memU s t (le_trans (le_max_left _ _) hs)
      rw [iteratedFDeriv_eq_of_eqOn hUo hΞX hp m]
      exact h s (le_trans (le_max_right _ _) hs) t)
  -- derivative bounds of `Y`
  set pr₁ : ℝ × ℝ × ℂ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℂ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ))) with hpr₁
  have hYeq : Y = (⇑pr₁ ∘ X) - id := funext fun p => by
    ext <;> simp [hpr₁, hX]
  have hYb : ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m Y (s, t)‖ ≤ C := fun m hm => by
    obtain ⟨C, s₁, h⟩ := hB m hm
    refine ⟨‖pr₁‖ * C + ‖ContinuousLinearMap.id ℝ (ℝ × ℝ)‖, max (S + 1) s₁, fun s hs t => ?_⟩
    have hp := memU s t (le_trans (le_max_left _ _) hs)
    have hXa : ContDiffAt ℝ ∞ X (s, t) := hXc _ hp
    rw [hYeq, iteratedFDeriv_sub_apply
      ((pr₁.contDiff.contDiffAt.comp _ hXa).of_le (by exact_mod_cast le_top))
      (contDiffAt_id.of_le (by exact_mod_cast le_top)),
      ContinuousLinearMap.iteratedFDeriv_comp_left pr₁ hXa (by exact_mod_cast le_top)]
    refine (norm_sub_le _ _).trans (add_le_add ?_
      (norm_iteratedFDeriv_le_of_hasFDerivAt_const _ (fun x => hasFDerivAt_id x) m hm _))
    exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      (mul_le_mul_of_nonneg_left (h s (le_trans (le_max_right _ _) hs) t) (norm_nonneg _))
  have hper : ∀ w : ℝ × ℝ, cylInf (w + (0, 1)).1 (w + (0, 1)).2 = cylInf w.1 w.2 := fun w => by
    have := cylInf_add_int w.1 w.2 1
    simpa using this
  intro m
  -- the `q` bound
  obtain ⟨C₁, s₁, hq_b⟩ : ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2) (s, t)‖ ≤ C := by
    obtain ⟨D, sD, -, hD⟩ := pow_bounds hYb m
    obtain ⟨Cg, hCg⟩ := strip_bound_le (fun k => strip_bound contDiff_cylInf hper lo hi k) m
    refine ⟨m ! * Cg * D ^ m, max (S + 1) sD, fun s hs t => ?_⟩
    have hp := memU s t (le_trans (le_max_left _ _) hs)
    have e1 : (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2) = q :=
      funext fun p => (hq_eq p).symm
    have e2 : iteratedFDeriv ℝ m q (s, t) =
        iteratedFDerivWithin ℝ m ((fun w : ℝ × ℝ => cylInf w.1 w.2) ∘ Y) U (s, t) := by
      rw [iteratedFDerivWithin_of_isOpen m hUo hp]
      exact iteratedFDeriv_eq_of_eqOn hUo (fun p hp => (hcylY p hp).symm) hp m
    rw [e1, e2]
    refine norm_iteratedFDerivWithin_comp_le (t := univ) contDiff_cylInf.contDiffOn hYon
      (by exact_mod_cast le_top) uniqueDiffOn_univ hUo.uniqueDiffOn (mapsTo_univ _ _) hp
      (fun i hi => ?_) (fun i h1 h2 => ?_)
    · rw [iteratedFDerivWithin_univ]
      exact hCg i hi _ (hYre _ hp) _
    · rw [iteratedFDerivWithin_of_isOpen i hUo hp]
      exact hD i h1 h2 s (le_trans (le_max_right _ _) hs) t
  -- the `v` bound
  obtain ⟨C₂, s₂, hv_b⟩ : ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (s, t)‖ ≤ C := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨r, S + 1, fun s hs t => ?_⟩
      have hp := memU s t hs
      rw [norm_iteratedFDeriv_zero]
      exact (hRv _ (le_trans (le_max_left _ _) (hZn _ hp))).le
    · obtain ⟨C, s₁, h⟩ := hB m hm
      set pr₂ : ℝ × ℝ × ℂ →L[ℝ] ℂ :=
        (ContinuousLinearMap.snd ℝ ℝ ℂ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)) with hpr₂
      refine ⟨‖pr₂‖ * C, max (S + 1) s₁, fun s hs t => ?_⟩
      have hp := memU s t (le_trans (le_max_left _ _) hs)
      have e : (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) = ⇑pr₂ ∘ X := funext fun p => rfl
      rw [e, ContinuousLinearMap.iteratedFDeriv_comp_left pr₂ (hXc _ hp)
        (by exact_mod_cast le_top)]
      exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
        (mul_le_mul_of_nonneg_left (h s (le_trans (le_max_right _ _) hs) t) (norm_nonneg _))
  refine ⟨max C₁ C₂, max s₁ s₂, fun s hs t =>
    ⟨(hq_b s (le_trans (le_max_left _ _) hs) t).trans (le_max_left _ _),
      (hv_b s (le_trans (le_max_right _ _) hs) t).trans (le_max_right _ _)⟩⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (f : ℂ → V 1) (df cf bf : ℝ) (hbf : 0 < bf)
    (hfa : ExpDecayCInfty (fun p : ℝ × ℝ => endA H f cylInf p - P.T * p.1 - df) bf)
    (hfw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H f cylInf p - P.x (P.T * p.2 + cf)) bf)
    (ψ v : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v)
    (hf : ∀ z, f z = u (ψ z) + N (ψ z) (v z))
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2)
    (hv0 : Tendsto v (cocompact ℂ) (𝓝 0)) :
    ∀ m : ℕ, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2) (s, t)‖ ≤ C ∧
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (s, t)‖ ≤ C :=
  FiniteEnergyPlane.tubeCoords_bounded_iteratedFDeriv_aux H hH J P u hu hu0 d b hb ha hw N hN hNinj M hM hNM f df cf bf hbf hfa hfw ψ v hψ hv hf hDψ hv0
