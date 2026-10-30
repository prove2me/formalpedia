-- Prove2me | solution 1 for FiniteEnergyPlane.cylEnd_tendsto_of_loops_tendsto_mod_phase
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T21:58:44.339237+00:00
-- url     : https://prove2.me/submissions/9f35401c-3bab-48d8-bed0-0640bda3d77a

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_cylEnd_shift
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem s2_cwLoop_scale (ρ t : ℝ) : cwLoop 0 ρ t = (ρ : ℂ) * cwLoop 0 1 t := by
  simp [cwLoop]

theorem s2_norm_cwLoop (t : ℝ) : ‖cwLoop 0 1 t‖ = 1 := by
  simp only [cwLoop, zero_add, Complex.ofReal_one, one_mul]
  rw [show (-((2 * π * t : ℝ) : ℂ)) * Complex.I = ((-(2 * π * t) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem s2_cylEnd_eq (s t : ℝ) :
    cylEnd s t = ((Real.exp (-(2 * π * s)) : ℝ) : ℂ) * cwLoop 0 1 t := by
  unfold cylEnd; rw [s2_cwLoop_scale]

theorem s2_norm_cylEnd (s t : ℝ) : ‖cylEnd s t‖ = Real.exp (-(2 * π * s)) := by
  rw [s2_cylEnd_eq, norm_mul, s2_norm_cwLoop, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

theorem s2_cylEnd_ne_zero (s t : ℝ) : cylEnd s t ≠ 0 := by
  rw [← norm_pos_iff, s2_norm_cylEnd]; exact Real.exp_pos _

theorem s2_cylEnd_add (s a t : ℝ) :
    cylEnd (s + a) t = ((Real.exp (-(2 * π * a)) : ℝ) : ℂ) * cylEnd s t := by
  rw [s2_cylEnd_eq, s2_cylEnd_eq, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3; ring

theorem s2_cylEnd_zero (s : ℝ) : cylEnd s 0 = ((Real.exp (-(2 * π * s)) : ℝ) : ℂ) := by
  rw [s2_cylEnd_eq]; simp [cwLoop]

theorem s2_cwLoop_periodic : Function.Periodic (cwLoop 0 1) 1 := by
  intro t
  simp only [cwLoop, zero_add, Complex.ofReal_one, one_mul]
  rw [show (-((2 * π * (t + 1) : ℝ) : ℂ)) * Complex.I =
      (-((2 * π * t : ℝ) : ℂ)) * Complex.I + -(2 * π * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]

theorem s2_contDiff_cwLoop : ContDiff ℝ ∞ (cwLoop 0 1) := by
  have h : cwLoop 0 1 = fun t : ℝ => Complex.exp (((-(2 * π) * t : ℝ) : ℂ) * Complex.I) := by
    funext t
    simp only [cwLoop, zero_add, Complex.ofReal_one, one_mul]
    congr 1
    push_cast
    ring
  rw [h]
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => (((-(2 * π) * t : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  exact Complex.contDiff_exp.comp (h1.mul contDiff_const)

/-- The cylindrical end map `p ↦ cylEnd p.1 p.2` is smooth. -/
theorem s2_contDiff_cyl : ContDiff ℝ ∞ (fun p : ℝ × ℝ => cylEnd p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => cylEnd p.1 p.2) =
      fun p => ((Real.exp (-(2 * π * p.1)) : ℝ) : ℂ) * cwLoop 0 1 p.2 :=
    funext fun p => s2_cylEnd_eq _ _
  rw [h]
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ((Real.exp (-(2 * π * p.1)) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_fst).neg))
  exact h1.mul (s2_contDiff_cwLoop.comp contDiff_snd)

/-- Trivial cylinders scale under positive real dilations. -/
theorem s2_trivialCylinder_real_mul {n : ℕ} {H : V n → ℝ} (P : ReebOrbit H) {r : ℝ} (hr : 0 < r)
    (ζ : ℂ) : trivialCylinder P ((r : ℂ) * ζ) = (r ^ (P.T / π)) • trivialCylinder P ζ := by
  unfold trivialCylinder
  rw [Complex.arg_real_mul _ hr, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
    Real.mul_rpow hr.le (norm_nonneg _), smul_smul]

/-- `C^∞_loc` convergence is inherited by a sequence agreeing on an open set with a shift of a
convergent sequence. -/
theorem s2_tendstoCInftyLocOn_of_eqOn_shift {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {U : Set X} (hU : IsOpen U)
    (f g : ℕ → X → Y) (h₀ : X → Y) (j₀ : ℕ)
    (heq : ∀ k, Set.EqOn (f (k + j₀)) (g k) U)
    (h : JHolomorphic.TendstoCInftyLocOn g h₀ U) : JHolomorphic.TendstoCInftyLocOn f h₀ U := by
  intro K hK hKc m
  have hg := Metric.tendstoUniformlyOn_iff.1 (h K hK hKc m)
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hg ε hε)
  refine eventually_atTop.2 ⟨N + j₀, fun k hk x hx => ?_⟩
  have hk' : k = (k - j₀) + j₀ := by omega
  have hd : iteratedFDeriv ℝ m (f k) x = iteratedFDeriv ℝ m (g (k - j₀)) x := by
    have he : f k =ᶠ[𝓝 x] g (k - j₀) := by
      rw [hk']
      refine (heq (k - j₀)).eventuallyEq_of_mem (hU.mem_nhds (hK hx)) |>.trans ?_
      rw [Nat.add_sub_cancel]
    exact (he.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds
  rw [hd]
  exact hN (k - j₀) (by omega) x hx

/-- `C^∞_loc` convergence passes to a tail and to an open subset. -/
theorem s2_tendstoCInftyLocOn_shift_mono {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {U W : Set X} (hWU : W ⊆ U)
    (f : ℕ → X → Y) (g : X → Y) (j₀ : ℕ) (h : JHolomorphic.TendstoCInftyLocOn f g U) :
    JHolomorphic.TendstoCInftyLocOn (fun k => f (k + j₀)) g W := by
  intro K hK hKc m
  have hg := Metric.tendstoUniformlyOn_iff.1 (h K (hK.trans hWU) hKc m)
  exact Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
    (tendsto_add_atTop_nat j₀).eventually (hg ε hε)

/-- `C^∞_loc` convergence on `ℝ × ℝ` follows from convergence on every strip `(-N, N) × ℝ`. -/
theorem s2_tendstoCInftyLocOn_univ_of_strips {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (f : ℕ → ℝ × ℝ → Y) (g : ℝ × ℝ → Y)
    (h : ∀ N : ℕ, JHolomorphic.TendstoCInftyLocOn f g (Set.Ioo (-(N : ℝ)) N ×ˢ Set.univ)) :
    JHolomorphic.TendstoCInftyLocOn f g Set.univ := by
  intro K _ hKc m
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).1 hKc.isBounded
  refine h (⌈R⌉₊ + 1) K (fun p hp => ?_) hKc m
  have hp' : ‖p‖ ≤ R := by simpa using hR hp
  have h1 : |p.1| ≤ ‖p‖ := by
    have := norm_fst_le p
    rwa [Real.norm_eq_abs] at this
  have h2 : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩ <;> push_cast <;>
    [linarith [neg_abs_le p.1]; linarith [le_abs_self p.1]]

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff Real

/-- A property that holds eventually along a subsequence of every sequence `s_k → ∞` holds for all
large `s`. -/
theorem hwzs_eventually_of_seq (Q : ℝ → Prop)
    (h : ∀ s : ℕ → ℝ, Tendsto s atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᶠ j in atTop, Q (s (φ j))) :
    ∃ s₁ : ℝ, ∀ s ≥ s₁, Q s := by
  by_contra hcon
  push_neg at hcon
  have h' : ∀ k : ℕ, ∃ s : ℝ, (k : ℝ) ≤ s ∧ ¬ Q s := fun k => by
    obtain ⟨s, hs, hq⟩ := hcon k
    exact ⟨s, hs, hq⟩
  choose s hs hq using h'
  obtain ⟨φ, -, hev⟩ := h s (tendsto_atTop_mono hs tendsto_natCast_atTop_atTop)
  obtain ⟨j, hj⟩ := hev.exists
  exact hq _ hj

/-- Derivatives of a map `1`-periodic in the second variable are `1`-periodic there. -/
theorem hwzs_iteratedFDeriv_fract {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × ℝ → F) (hf : ∀ p : ℝ × ℝ, f (p + (0, 1)) = f p) (m : ℕ) (s t : ℝ) :
    iteratedFDeriv ℝ m f (s, t) = iteratedFDeriv ℝ m f (s, Int.fract t) := by
  have hper : ∀ s : ℝ, Function.Periodic (fun t => f (s, t)) 1 := fun s t => by
    have := hf (s, t)
    simp only [Prod.mk_add_mk, add_zero] at this
    exact this
  have hfun : (fun z : ℝ × ℝ => f (z + (0, (⌊t⌋ : ℝ)))) = f := by
    funext z
    have := (hper z.1).int_mul ⌊t⌋ z.2
    simp only [mul_one] at this
    rw [show z + (0, (⌊t⌋ : ℝ)) = (z.1, z.2 + ⌊t⌋) by ext <;> simp]
    exact this
  have h1 : (s, t) = (s, Int.fract t) + (0, (⌊t⌋ : ℝ)) := by
    ext <;> simp [Int.fract_add_floor]
  rw [h1, ← iteratedFDeriv_comp_add_right, hfun]

theorem cylEnd_tendsto_of_loops_tendsto_mod_phase_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (hloop : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedDeriv j (loopInS H u (cwLoop 0 r)) t -
        iteratedDeriv j (fun t => P.x (σ * P.T * t + c')) t‖ ≤ ε) :
    (∃ s₀ : ℝ, ContDiffOn ℝ ∞ (endA H u cylEnd) (Set.Ioi s₀ ×ˢ Set.univ) ∧
        ContDiffOn ℝ ∞ (endW H u cylEnd) (Set.Ioi s₀ ×ˢ Set.univ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
        ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1) (s, t)‖ ≤ ε) ∧
      ∀ m : ℕ, ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
        ‖iteratedFDeriv ℝ j
          (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (σ * P.T * p.2 + c')) (s, t)‖ ≤ ε := by
  obtain ⟨-, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hle : ∀ m : ℕ, ((m : ℕ∞) : WithTop ℕ∞) ≤ ∞ := fun m => by exact_mod_cast le_top
  have hloop0 : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ c' : ℝ, ∀ t : ℝ,
      ‖loopInS H u (cwLoop 0 r) t - P.x (σ * P.T * t + c')‖ ≤ ε := by
    intro ε hε
    filter_upwards [hloop 0 ε hε] with r hr
    obtain ⟨c', hc'⟩ := hr
    exact ⟨c', fun t => by simpa using hc' 0 le_rfl t⟩
  -- smoothness on `(0, ∞) × ℝ`
  set U : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.univ with hUdef
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hcylU : Set.MapsTo (fun p : ℝ × ℝ => cylEnd p.1 p.2) U (ball 0 1 \ {0}) := by
    intro p hp
    refine ⟨?_, s2_cylEnd_ne_zero _ _⟩
    have hp1 : 0 < p.1 := hp.1
    rw [mem_ball_zero_iff, s2_norm_cylEnd]
    have := Real.exp_lt_exp.2 (show -(2 * π * p.1) < 0 by nlinarith [Real.pi_pos])
    rwa [Real.exp_zero] at this
  have huc : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => u (cylEnd p.1 p.2)) U :=
    hu.1.comp s2_contDiff_cyl.contDiffOn hcylU
  have hu0 : Set.MapsTo (fun p : ℝ × ℝ => u (cylEnd p.1 p.2)) U {y | y ≠ 0} := fun p hp =>
    hu.2.1 _ (hcylU hp)
  have hA : ContDiffOn ℝ ∞ (endA H u cylEnd) U := haCs.comp huc hu0
  have hW : ContDiffOn ℝ ∞ (endW H u cylEnd) U := hprojs.comp huc hu0
  have hcylper : ∀ s t : ℝ, cylEnd s (t + 1) = cylEnd s t := by
    intro s t; rw [s2_cylEnd_eq, s2_cylEnd_eq, s2_cwLoop_periodic]
  have hK : IsCompact (({0} : Set ℝ) ×ˢ Set.Icc (0 : ℝ) 1) := isCompact_singleton.prod isCompact_Icc
  have hKmem : ∀ t : ℝ, ((0 : ℝ), Int.fract t) ∈ ({0} : Set ℝ) ×ˢ Set.Icc (0 : ℝ) 1 :=
    fun t => ⟨rfl, Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hshiftmem : ∀ (a t : ℝ), 0 < a → ((0 : ℝ), Int.fract t) + (a, 0) ∈ U := fun a t ha => by
    show 0 < ((0 : ℝ), Int.fract t).1 + (a, (0 : ℝ)).1 ∧ _
    exact ⟨by simpa using ha, trivial⟩
  have hshift : ∀ (a t : ℝ), ((0 : ℝ), Int.fract t) + (a, 0) = (a, Int.fract t) := fun a t => by
    ext <;> simp
  refine ⟨⟨0, hA, hW⟩, ?_, ?_⟩
  · -- the `a`-coordinate
    intro m hm ε hε
    set g : ℝ × ℝ → ℝ := fun p => endA H u cylEnd p - σ * P.T * p.1 with hgdef
    have hgper : ∀ p : ℝ × ℝ, g (p + (0, 1)) = g p := by
      intro p
      simp only [hgdef, endA, Prod.fst_add, Prod.snd_add, add_zero, hcylper]
    refine hwzs_eventually_of_seq (fun s => ∀ t : ℝ, ‖iteratedFDeriv ℝ m g (s, t)‖ ≤ ε) ?_
    intro s hs
    obtain ⟨φ, hφ, c, hcA, -⟩ :=
      exists_subseq_tendstoCInftyLocOn_cylEnd_shift H hH J hJ u hu P σ hσ hloop0 s hs
    refine ⟨φ, hφ, ?_⟩
    have hunif := Metric.tendstoUniformlyOn_iff.1 (hcA _ (Set.subset_univ _) hK m) ε hε
    have hpos : ∀ᶠ j in atTop, 0 < s (φ j) :=
      (hs.comp hφ.tendsto_atTop).eventually (eventually_gt_atTop 0)
    filter_upwards [hunif, hpos] with j hj hjpos t
    set a : ℝ × ℝ := (s (φ j), 0) with hadef
    set G : ℝ × ℝ → ℝ := fun p => endA H u cylEnd (p + a) - endA H u cylEnd a with hGdef
    set ℓ : ℝ × ℝ → ℝ := fun p => σ * P.T * p.1 with hℓdef
    set x : ℝ × ℝ := ((0 : ℝ), Int.fract t) with hxdef
    have hGc : ContDiffAt ℝ m G x := by
      have h1 : ContDiffAt ℝ ∞ (endA H u cylEnd) (x + a) :=
        hA.contDiffAt (hUo.mem_nhds (hshiftmem _ t hjpos))
      exact ((h1.comp x (contDiffAt_id.add contDiffAt_const)).sub contDiffAt_const).of_le (hle m)
    have hℓc : ContDiffAt ℝ m ℓ x :=
      ((contDiff_const.mul contDiff_fst).contDiffAt).of_le (hle m)
    have hfun : (fun z => g (z + a)) = (G - ℓ) + fun _ => endA H u cylEnd a - σ * P.T * a.1 := by
      funext z
      simp only [hgdef, hGdef, hℓdef, Pi.add_apply, Pi.sub_apply, Prod.fst_add]
      ring
    have key : iteratedFDeriv ℝ m g (s (φ j), t) =
        iteratedFDeriv ℝ m G x - iteratedFDeriv ℝ m ℓ x := by
      rw [hwzs_iteratedFDeriv_fract g hgper, ← hshift (s (φ j)) t, ← hxdef,
        ← iteratedFDeriv_comp_add_right, hfun,
        iteratedFDeriv_add_apply (f := G - ℓ) (by exact hGc.sub hℓc) contDiffAt_const,
        iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, add_zero,
        iteratedFDeriv_sub_apply hGc hℓc]
    rw [key, ← dist_eq_norm, dist_comm]
    exact (hj x (hKmem t)).le
  · -- the `w`-coordinate
    intro m ε hε
    refine hwzs_eventually_of_seq (fun s => ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j
        (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (σ * P.T * p.2 + c')) (s, t)‖ ≤ ε) ?_
    intro s hs
    obtain ⟨φ, hφ, c, -, hcW⟩ :=
      exists_subseq_tendstoCInftyLocOn_cylEnd_shift H hH J hJ u hu P σ hσ hloop0 s hs
    refine ⟨φ, hφ, ?_⟩
    have hall : ∀ᶠ k in atTop, ∀ j ∈ Finset.range (m + 1),
        ∀ x ∈ ({0} : Set ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
          dist (iteratedFDeriv ℝ j (fun p : ℝ × ℝ => P.x (σ * P.T * p.2 + c)) x)
            (iteratedFDeriv ℝ j (fun p : ℝ × ℝ => endW H u cylEnd (p + (s (φ k), 0))) x) < ε :=
      (Finset.range (m + 1)).eventually_all.2 fun j _ =>
        Metric.tendstoUniformlyOn_iff.1 (hcW _ (Set.subset_univ _) hK j) ε hε
    have hpos : ∀ᶠ k in atTop, 0 < s (φ k) :=
      (hs.comp hφ.tendsto_atTop).eventually (eventually_gt_atTop 0)
    filter_upwards [hall, hpos] with k hk hkpos
    refine ⟨c, fun j hj t => ?_⟩
    set a : ℝ × ℝ := (s (φ k), 0) with hadef
    set X : ℝ × ℝ → V n := fun p => P.x (σ * P.T * p.2 + c) with hXdef
    set gW : ℝ × ℝ → V n := fun p => endW H u cylEnd p - X p with hgWdef
    set Wk : ℝ × ℝ → V n := fun p => endW H u cylEnd (p + a) with hWkdef
    set x : ℝ × ℝ := ((0 : ℝ), Int.fract t) with hxdef
    have hXper : ∀ τ : ℝ, P.x (τ + σ * P.T) = P.x τ := by
      intro τ
      rcases hσ with h | h
      · rw [h, one_mul]; exact P.periodic τ
      · rw [h, neg_one_mul, ← sub_eq_add_neg]
        have := P.periodic (τ - P.T)
        rw [sub_add_cancel] at this
        exact this.symm
    have hgper : ∀ p : ℝ × ℝ, gW (p + (0, 1)) = gW p := by
      intro p
      simp only [hgWdef, hXdef, endW, Prod.fst_add, Prod.snd_add, add_zero, hcylper]
      rw [show σ * P.T * (p.2 + 1) + c = σ * P.T * p.2 + c + σ * P.T by ring, hXper]
    have hXc : ContDiff ℝ ∞ X :=
      (ReebOrbit.contDiff_x H hH P).comp ((contDiff_const.mul contDiff_snd).add contDiff_const)
    have hWkc : ContDiffAt ℝ j Wk x := by
      have h1 : ContDiffAt ℝ ∞ (endW H u cylEnd) (x + a) :=
        hW.contDiffAt (hUo.mem_nhds (hshiftmem _ t hkpos))
      exact (h1.comp x (contDiffAt_id.add contDiffAt_const)).of_le (hle j)
    have hfun : (fun z => gW (z + a)) = Wk - X := by
      funext z
      simp only [hgWdef, hWkdef, hXdef, hadef, Pi.sub_apply, Prod.snd_add, add_zero]
    have key : iteratedFDeriv ℝ j gW (s (φ k), t) =
        iteratedFDeriv ℝ j Wk x - iteratedFDeriv ℝ j X x := by
      rw [hwzs_iteratedFDeriv_fract gW hgper, ← hshift (s (φ k)) t, ← hxdef,
        ← iteratedFDeriv_comp_add_right, hfun,
        iteratedFDeriv_sub_apply hWkc ((hXc.of_le (hle j)).contDiffAt)]
    show ‖iteratedFDeriv ℝ j gW (s (φ k), t)‖ ≤ ε
    rw [key, ← dist_eq_norm, dist_comm]
    exact (hk j (Finset.mem_range.2 (by omega)) x (hKmem t)).le

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (hloop : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedDeriv j (loopInS H u (cwLoop 0 r)) t -
        iteratedDeriv j (fun t => P.x (σ * P.T * t + c')) t‖ ≤ ε) :
    (∃ s₀ : ℝ, ContDiffOn ℝ ∞ (endA H u cylEnd) (Set.Ioi s₀ ×ˢ Set.univ) ∧
        ContDiffOn ℝ ∞ (endW H u cylEnd) (Set.Ioi s₀ ×ˢ Set.univ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
        ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1) (s, t)‖ ≤ ε) ∧
      ∀ m : ℕ, ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
        ‖iteratedFDeriv ℝ j
          (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (σ * P.T * p.2 + c')) (s, t)‖ ≤ ε :=
  cylEnd_tendsto_of_loops_tendsto_mod_phase_aux H hH J hJ u hu P σ hσ hloop
