-- Prove2me | solution 1 for FiniteEnergyPlane.bounded_iteratedFDeriv_endA_endW
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T19:16:15.097164+00:00
-- url     : https://prove2.me/submissions/a50cbc2d-5029-4c9e-af17-ba86bec94d0f

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x



/-!
# R′ generic helpers: derivative bounds on `ℝ × ℝ` (Mathlib only)
-/

namespace FiniteEnergyPlane

open Set
open scoped ContDiff

namespace DGA3R

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

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

end DGA3R

end FiniteEnergyPlane

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

/-- Equal functions on an open set have equal iterated derivatives there. -/
lemma iteratedFDeriv_eq_of_eqOn {f g : E → F} {U : Set E} (hU : IsOpen U) (h : EqOn f g U)
    {x : E} (hx : x ∈ U) (n : ℕ) : iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  rw [← iteratedFDerivWithin_of_isOpen n hU hx, ← iteratedFDerivWithin_of_isOpen n hU hx]
  exact iteratedFDerivWithin_congr h hx n

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

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (f : ℂ → V 1) (df cf bf : ℝ)
    (hfa : ExpDecayCInfty (fun p : ℝ × ℝ => endA H f cylInf p - P.T * p.1 - df) bf)
    (hfw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H f cylInf p - P.x (P.T * p.2 + cf)) bf)
    (hbf : 0 < bf) (m : ℕ) (hm : 1 ≤ m) :
    ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => (endA H f cylInf p, endW H f cylInf p)) (s, t)‖
        ≤ C :=
  FiniteEnergyPlane.DGA3R.endAW_bound H hH P f df cf bf hfa hfw hbf m hm
