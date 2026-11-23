-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.rowSums
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:58.833565+00:00
-- url     : https://prove2.me/submissions/94f684e1-0dcc-4add-a48a-0c0d007747bf

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution : RowSums := by
  intro C₁ C₂
  refine ⟨|C₁| * (1 + |C₁|) + 2 * |C₂|, ?_⟩
  intro B U Pl X Mv _ _ _ _ _ _ _ _ vol Z UP jj χ bb uu tgt μ ω ω₀ q a ρ hq hρ hPl hjj hU hvol hVB hμ hW hZ hχZ
    hχ1 hUP hleak htgt hω
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  set δ : ℝ := (q : ℝ) ^ (1 - (ρ : ℤ)) with hδ
  have hδ0 : 0 < δ := zpow_pos hq0 _
  have hδ1 : δ ≤ 1 := zpow_le_one_of_nonpos₀ hq1 (by omega)
  have hU0 : (0 : ℝ) < Fintype.card U := by exact_mod_cast hU
  set N : ℝ := (Fintype.card U : ℝ) / (q : ℝ) ^ a with hN
  have hN0 : 0 < N := by positivity
  set VB : ℝ := ∑ b, vol b with hVBdef

  have fib : ∀ g : B → U → ℂ, ∑ m, (μ m : ℂ) * g (bb m) (uu m)
      = ∑ b, ∑ u ∈ Z, ((vol b / (VB * N) : ℝ) : ℂ) * g b u := by
    intro g
    rw [← Finset.sum_fiberwise (s := univ) (g := fun m => (bb m, uu m)), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun u => u ∈ Z)]
    have hz : ∑ u ∈ univ.filter (fun u => ¬ u ∈ Z),
        ∑ m ∈ univ.filter (fun m => (bb m, uu m) = (b, u)), (μ m : ℂ) * g (bb m) (uu m) = 0 := by
      refine Finset.sum_eq_zero fun u hu => ?_
      have hu' : u ∉ Z := (Finset.mem_filter.mp hu).2
      have h0 := hW b u
      rw [if_neg hu'] at h0
      refine Finset.sum_eq_zero fun m hm => ?_
      have hm' : bb m = b ∧ uu m = u := by simpa using (Finset.mem_filter.mp hm).2
      have : μ m = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hμ i)).mp h0 m (by simp [hm'.1, hm'.2])
      simp [this]
    rw [hz, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun u hu => ?_
    have h0 := hW b u
    rw [if_pos hu] at h0
    rw [← h0]
    push_cast
    rw [Finset.sum_mul]
    have hf : univ.filter (fun m => (bb m, uu m) = (b, u)) = univ.filter (fun m => bb m = b ∧ uu m = u) := by
      ext m; simp
    rw [hf]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := (Finset.mem_filter.mp hm).2
    rw [hm'.1, hm'.2]
  have fibR : ∀ g : B → U → ℝ, ∑ m, μ m * g (bb m) (uu m) = ∑ b, ∑ u ∈ Z, vol b / (VB * N) * g b u := by
    intro g
    apply Complex.ofReal_injective
    push_cast
    have := fib (fun b u => (g b u : ℂ))
    push_cast at this
    exact this
  have volsum : ∀ t : ℝ, ∑ b, vol b / (VB * N) * t = t / N := by
    intro t
    rw [← Finset.sum_mul, ← Finset.sum_div, ← hVBdef]
    field_simp

  have hT : ∑ m, μ m = (Z.card : ℝ) / N := by
    have := fibR (fun _ _ => 1)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at this
    rw [this, ← volsum (Z.card : ℝ)]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hTerr : |(Z.card : ℝ) / N - 1| ≤ |C₁| * δ := by
    have : (Z.card : ℝ) / N - 1 = ((Z.card : ℝ) - N) / N := by field_simp
    rw [this, abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    calc |(Z.card : ℝ) - N| ≤ C₁ * δ * N := hZ
      _ ≤ |C₁| * δ * N := by gcongr; exact le_abs_self _
  have hZN : (Z.card : ℝ) / N ≤ 1 + |C₁| := by
    have := (abs_le.mp hTerr).2
    have h2 : |C₁| * δ ≤ |C₁| := mul_le_of_le_one_right (abs_nonneg _) hδ1
    linarith

  have hP : ∀ P, ∑ m, μ m * (if uu m ∈ UP P then 1 else 0) ≤ |C₂| * δ := by
    intro P
    have := fibR (fun _ u => if u ∈ UP P then 1 else 0)
    rw [this]
    have h1 : ∀ b, ∑ u ∈ Z, vol b / (VB * N) * (if u ∈ UP P then (1 : ℝ) else 0)
        = vol b / (VB * N) * ((Z ∩ UP P).card : ℝ) := by
      intro b
      rw [← Finset.mul_sum, Finset.sum_ite_mem]; simp
    simp only [h1]
    rw [volsum, div_le_iff₀ hN0]
    have hpw : (q : ℝ) ^ jj P * ((q : ℝ) ^ (jj P * ρ))⁻¹ ≤ δ := by
      obtain ⟨j', hj'⟩ := Nat.exists_eq_add_of_le (hjj P)
      have e : (q : ℝ) ^ jj P * ((q : ℝ) ^ (jj P * ρ))⁻¹ = δ ^ jj P := by
        rw [hδ, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hq0.ne', ← zpow_natCast, ← zpow_mul]
        congr 1; push_cast; ring
      rw [e, hj', pow_add, pow_one]
      exact mul_le_of_le_one_right hδ0.le (pow_le_one₀ hδ0.le hδ1)
    calc ((Z ∩ UP P).card : ℝ) ≤ C₂ * (q : ℝ) ^ jj P * (((UP P).card : ℝ) / (q : ℝ) ^ a) := hleak P
      _ = C₂ * ((q : ℝ) ^ jj P * ((q : ℝ) ^ (jj P * ρ))⁻¹) * N := by
          rw [hUP P, hN]; field_simp
      _ ≤ |C₂| * ((q : ℝ) ^ jj P * ((q : ℝ) ^ (jj P * ρ))⁻¹) * N := by
          gcongr; exact le_abs_self _
      _ ≤ |C₂| * δ * N := by gcongr
  have hL : ∑ m ∈ univ.filter (fun m => tgt m = none), μ m ≤ 2 * |C₂| * δ := by
    calc ∑ m ∈ univ.filter (fun m => tgt m = none), μ m
        ≤ ∑ m ∈ univ.filter (fun m => tgt m = none), ∑ P, μ m * (if uu m ∈ UP P then 1 else 0) := by
          refine Finset.sum_le_sum fun m hm => ?_
          obtain ⟨P, hPm⟩ := htgt m (Finset.mem_filter.mp hm).2
          calc μ m = μ m * (if uu m ∈ UP P then 1 else 0) := by rw [if_pos hPm, mul_one]
            _ ≤ _ := Finset.single_le_sum (f := fun P => μ m * (if uu m ∈ UP P then (1 : ℝ) else 0))
                  (fun P' _ => mul_nonneg (hμ m) (by split_ifs <;> norm_num)) (Finset.mem_univ P)
      _ ≤ ∑ m, ∑ P, μ m * (if uu m ∈ UP P then 1 else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun m _ _ =>
            Finset.sum_nonneg fun P' _ => mul_nonneg (hμ m) (by split_ifs <;> norm_num)
      _ = ∑ P, ∑ m, μ m * (if uu m ∈ UP P then 1 else 0) := Finset.sum_comm
      _ ≤ ∑ _P : Pl, |C₂| * δ := Finset.sum_le_sum fun P _ => hP P
      _ = (Fintype.card Pl : ℝ) * (|C₂| * δ) := by simp
      _ ≤ 2 * (|C₂| * δ) := by
          refine mul_le_mul_of_nonneg_right (by exact_mod_cast hPl) (by positivity)
      _ = 2 * |C₂| * δ := by ring
  have hL0 : 0 ≤ ∑ m ∈ univ.filter (fun m => tgt m = none), μ m := Finset.sum_nonneg fun m _ => hμ m

  have split : ∀ F : Mv → ℂ, ∑ x, ∑ m ∈ univ.filter (fun m => tgt m = some x), F m
      = ∑ m, F m - ∑ m ∈ univ.filter (fun m => tgt m = none), F m := by
    intro F
    rw [← Finset.sum_fiberwise (s := univ) (g := tgt) (f := F), Fintype.sum_option]; ring
  have splitR : ∑ x, ∑ m ∈ univ.filter (fun m => tgt m = some x), μ m
      = ∑ m, μ m - ∑ m ∈ univ.filter (fun m => tgt m = none), μ m := by
    rw [← Finset.sum_fiberwise (s := univ) (g := tgt) (f := μ), Fintype.sum_option]; ring
  constructor
  · rw [splitR, hT]
    have h1 := abs_le.mp hTerr
    have h3 : |C₁| * δ ≤ |C₁| * (1 + |C₁|) * δ := by
      have : |C₁| ≤ |C₁| * (1 + |C₁|) := le_mul_of_one_le_right (abs_nonneg _) (by linarith [abs_nonneg C₁])
      gcongr
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2]
  · have e1 : ∑ x, ((∑ m ∈ univ.filter (fun m => tgt m = some x), μ m : ℝ) : ℂ) * ω x
        = ω₀ * ∑ x, ∑ m ∈ univ.filter (fun m => tgt m = some x), (μ m : ℂ) * χ (bb m) (uu m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      push_cast
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [hω m x (Finset.mem_filter.mp hm).2]; ring
    rw [e1, split, norm_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have n1 : ‖∑ m, (μ m : ℂ) * χ (bb m) (uu m)‖ ≤ |C₁| * (1 + |C₁|) * δ := by
      rw [fib]
      calc ‖∑ b, ∑ u ∈ Z, ((vol b / (VB * N) : ℝ) : ℂ) * χ b u‖
          ≤ ∑ b, ‖∑ u ∈ Z, ((vol b / (VB * N) : ℝ) : ℂ) * χ b u‖ := norm_sum_le _ _
        _ ≤ ∑ b, vol b / (VB * N) * (|C₁| * δ * (Z.card : ℝ)) := by
            refine Finset.sum_le_sum fun b _ => ?_
            rw [← Finset.mul_sum, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by have := hvol b; positivity)]
            refine mul_le_mul_of_nonneg_left ?_ (by have := hvol b; positivity)
            calc ‖∑ u ∈ Z, χ b u‖ ≤ C₁ * δ * (Z.card : ℝ) := hχZ b
              _ ≤ |C₁| * δ * (Z.card : ℝ) := by gcongr; exact le_abs_self _
        _ = |C₁| * δ * ((Z.card : ℝ) / N) := by rw [volsum]; ring
        _ ≤ |C₁| * δ * (1 + |C₁|) := by gcongr
        _ = _ := by ring
    have n2 : ‖∑ m ∈ univ.filter (fun m => tgt m = none), (μ m : ℂ) * χ (bb m) (uu m)‖ ≤ 2 * |C₂| * δ := by
      calc _ ≤ ∑ m ∈ univ.filter (fun m => tgt m = none), ‖(μ m : ℂ) * χ (bb m) (uu m)‖ := norm_sum_le _ _
        _ = ∑ m ∈ univ.filter (fun m => tgt m = none), μ m := by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [norm_mul, hχ1, mul_one, Complex.norm_real, Real.norm_of_nonneg (hμ m)]
        _ ≤ _ := hL
    calc _ ≤ ‖∑ m, (μ m : ℂ) * χ (bb m) (uu m)‖
          + ‖∑ m ∈ univ.filter (fun m => tgt m = none), (μ m : ℂ) * χ (bb m) (uu m)‖ := norm_sub_le _ _
      _ ≤ |C₁| * (1 + |C₁|) * δ + 2 * |C₂| * δ := add_le_add n1 n2
      _ = _ := by ring
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
