-- Prove2me | solution 1 for DerivativeChainGiniCircle.actual_degree40_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:10:25.937548+00:00
-- url     : https://prove2.me/submissions/d8161549-99c0-4c1c-adb9-296b764f582a

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Definitions.Def_DerivativeChainGini_GiniCandidateB
import Definitions.Def_DerivativeChainGini_GiniCircleCounterexample
import Definitions.Def_DerivativeChainGini_GiniFamilyTransport
import Definitions.Def_DerivativeChainGini_GiniPolygon36
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainDivisorAnchor
end DerivativeChainDivisorAnchor
namespace DerivativeChainGini
end DerivativeChainGini
namespace DerivativeChainGiniCircle
end DerivativeChainGiniCircle
namespace DerivativeChainGiniFamily
end DerivativeChainGiniFamily
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainGiniFamily
noncomputable section
variable {ι : Type} [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable
























theorem child_gini (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (ε : ℝ) :
    DerivativeChainContinuation.finiteGini (childMass ε) (point z) =
      (1-ε)^2 * DerivativeChainContinuation.finiteGini (fun _ : ι => 1/(Fintype.card ι : ℝ)) z +
        2*ε*(1-ε) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [DerivativeChainContinuation.finiteGini, Fintype.sum_option, childMass, point, hz,
    norm_neg, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  field_simp
  <;> ring

end
end DerivativeChainGiniFamily


set_option autoImplicit false
open scoped BigOperators
open Polynomial
namespace DerivativeChainGiniFamily
noncomputable section






theorem base_monic (n : ℕ) : (base n).Monic := by
  simpa [base] using monic_X_pow_sub_C (R := ℂ) 1 (n := n+2) (by omega)







theorem slot_root (n : ℕ) (i : Slots n) : (i : ℂ)^(n+2) = 1 := by
  have hi := (mem_roots (base_monic n).ne_zero).mp (Multiset.coe_mem (x := i))
  simpa [base, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] using hi

theorem slot_norm (n : ℕ) (i : Slots n) : ‖(i : ℂ)‖ = 1 := by
  have hi := congrArg norm (slot_root n i)
  simp only [norm_pow, norm_one] at hi
  exact (pow_left_inj₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1) (by omega : n+2 ≠ 0)).mp (by simpa using hi)

theorem base_roots_sum (n : ℕ) : (base n).roots.sum = 0 := by
  have h := (IsAlgClosed.splits (base n)).nextCoeff_eq_neg_sum_roots_of_monic (base_monic n)
  have hn : (base n).nextCoeff = 0 := by
    rw [nextCoeff, base_degree]
    simp [base, show n+2 ≠ 0 by omega,
      show n+2-1 = n+1 by omega, show n+1 ≠ n+2 by omega, show n+1 ≠ 0 by omega]
    simp only [coeff_one, show n+1 ≠ 0 by omega, if_false]
  rw [hn] at h
  exact neg_eq_zero.mp h.symm

















end
end DerivativeChainGiniFamily


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainContinuation
namespace DerivativeChainGiniFamily
noncomputable section










theorem slot_sum_map (n : ℕ) (f : ℂ → ℝ) :
    ∑ i : Slots n, f (rootSlot n i) = ((base n).roots.map f).sum := by
  change ((Finset.univ : Finset (Slots n)).val.map (fun i : Slots n => f (i : ℂ))).sum = _
  rw [Multiset.map_univ]













































end
end DerivativeChainGiniFamily


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section



theorem multiset_sum_coe (s : Multiset ℂ) (f : ℂ → ℝ) :
    (s.map f).sum = ∑ i : s, f (i:ℂ) := by
  symm
  change ((Finset.univ : Finset s).val.map (fun i : s => f (i:ℂ))).sum = _
  rw [Multiset.map_univ]







































end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily DerivativeChainDivisorAnchor
namespace DerivativeChainGiniCircle
noncomputable section




theorem unityRoot_primitive : IsPrimitiveRoot unityRoot 36 :=
  Complex.isPrimitiveRoot_exp 36 (by norm_num)

theorem unityRoot_norm : ‖unityRoot‖=1 := unityRoot_primitive.norm'_eq_one (by norm_num)

theorem polygonPoint_norm (i : ZMod 36) : ‖polygonPoint i‖=1 := by
  simp only [polygonPoint, norm_pow, unityRoot_norm, one_pow]

theorem polygonPoint_add (i j : ZMod 36) : polygonPoint (i+j)=polygonPoint i*polygonPoint j := by
  rw [polygonPoint, ZMod.val_add, ← pow_eq_pow_mod (i.val+j.val) unityRoot_primitive.pow_eq_one, pow_add]
  rfl

theorem roots36_multiset : (base 34).roots = (Multiset.range 36).map (fun j => unityRoot^j) := by
  have h := unityRoot_primitive.nthRoots_eq (α := (1:ℂ)) (a := (1:ℂ)) (by norm_num : (1:ℂ)^36=1)
  simpa only [nthRoots, base, C_1, mul_one] using h

theorem sum_zmod36_range (f : ℕ → ℝ) :
    (∑ i : ZMod 36, f i.val) = ∑ j ∈ Finset.range 36, f j := by
  change (∑ i : Fin 36, f i.val) = _
  exact Fin.sum_univ_eq_sum_range f 36

theorem rootSum36 (f : ℂ → ℝ) : rootSum (base 34) f = ∑ i : ZMod 36, f (polygonPoint i) := by
  unfold rootSum
  rw [roots36_multiset, Multiset.map_map]
  simp only [polygonPoint]
  rw [sum_zmod36_range (fun j => f (unityRoot^j))]
  rfl

theorem polygon_row_sum (i : ZMod 36) :
    (∑ j : ZMod 36, ‖polygonPoint i-polygonPoint j‖) = ∑ j : ZMod 36, ‖1-polygonPoint j‖ := by
  calc
    _ = ∑ j : ZMod 36, ‖polygonPoint i-polygonPoint (i+j)‖ :=
      ((Equiv.addLeft i).bijective.sum_comp (fun j => ‖polygonPoint i-polygonPoint j‖)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [polygonPoint_add, show polygonPoint i-polygonPoint i*polygonPoint j = polygonPoint i*(1-polygonPoint j) by ring,
        norm_mul, polygonPoint_norm, one_mul]

theorem polygon_pair_sum : rootPairSum (base 34) (base 34) =
    36*(∑ j : ZMod 36, ‖1-polygonPoint j‖) := by
  unfold rootPairSum
  simp_rw [rootSum36, polygon_row_sum]
  simp

theorem chord_value (j : ℕ) (hj : j < 36) :
    ‖1-unityRoot^j‖ = 2*Real.sin (Real.pi*j/36) := by
  have he : unityRoot^j = Complex.exp (Complex.I*((2*Real.pi*j/36:ℝ):ℂ)) := by
    rw [unityRoot, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he, norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2*Real.pi*(j:ℝ)/36)/2=Real.pi*j/36 by ring]
  rw [Real.norm_eq_abs, abs_of_nonneg]
  apply mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · positivity
  · have hjR : (j:ℝ) < 36 := by exact_mod_cast hj
    nlinarith [Real.pi_pos]

theorem chord_sum_sines :
    (∑ j : ZMod 36, ‖1-polygonPoint j‖) = 2*(∑ j ∈ Finset.range 36, Real.sin (Real.pi*j/36)) := by
  rw [show (∑ j : ZMod 36, ‖1-polygonPoint j‖) =
    ∑ j ∈ Finset.range 36, ‖1-unityRoot^j‖ from sum_zmod36_range (fun j => ‖1-unityRoot^j‖)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact chord_value j (Finset.mem_range.mp hj)

theorem sin_half_angle_pos : 0 < Real.sin (Real.pi/72) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

theorem sum_sines36 : (∑ j ∈ Finset.range 36, Real.sin (Real.pi*j/36)) =
    Real.cos (Real.pi/72)/Real.sin (Real.pi/72) := by
  have h := Real.sin_mul_sum_sin 36 (Real.pi/36) 0
  norm_num only at h
  have h0 : (Real.pi/36)/2=Real.pi/72 := by ring
  have h1 : (36:ℝ)*(Real.pi/36)/2=Real.pi/2 := by ring
  have h2 : ((35:ℝ)*(Real.pi/36)/2)=Real.pi/2-Real.pi/72 := by ring
  simp only [h0, h1, h2, Real.sin_pi_div_two, one_mul] at h
  simp only [add_zero] at h
  rw [Real.sin_pi_div_two_sub] at h
  have he (i : ℕ) : Real.pi/36*i=Real.pi*i/36 := by ring
  simp only [he] at h
  exact (eq_div_iff sin_half_angle_pos.ne').mpr (by simpa only [mul_comm] using h)

theorem empiricalGini_pair (P : ℂ[X]) : empiricalGini P = rootPairSum P P/(P.natDegree:ℝ)^2 := by
  unfold empiricalGini empiricalExpectation rootPairSum rootSum
  simp_rw [multiset_sum_coe]
  simp only [← Finset.sum_div, div_div, pow_two]

theorem polygon_gini_exact : empiricalGini (base 34) =
    (1/18:ℝ)*Real.cos (Real.pi/72)/Real.sin (Real.pi/72) := by
  rw [empiricalGini_pair, base_degree, polygon_pair_sum, chord_sum_sines, sum_sines36]
  norm_num
  ring

theorem uniformGini34_actual : uniformGini 34 = empiricalGini (base 34) := by
  rw [empiricalGini_pair, base_degree]
  unfold uniformGini DerivativeChainContinuation.finiteGini rootPairSum rootSum rootSlot
  simp_rw [multiset_sum_coe]
  norm_num
  simp only [← Finset.mul_sum]
  ring

end
end DerivativeChainGiniCircle


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily DerivativeChainDivisorAnchor DerivativeChainContinuation
namespace DerivativeChainGiniCircle
noncomputable section



theorem source_monic : source.Monic := (monic_X_pow _).mul (base_monic 34)

theorem source_degree : source.natDegree=40 := by
  rw [source, natDegree_mul (pow_ne_zero _ X_ne_zero) (base_monic 34).ne_zero, natDegree_X_pow, base_degree]

theorem source_roots : source.roots = 4 • ({0}:Multiset ℂ)+(base 34).roots := by
  rw [source, roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (base_monic 34).ne_zero), roots_X_pow]

theorem source_root_law (f : ℂ → ℝ) :
    (∑ i : Option (Slots 34), childMass (1/10) i*f (point (rootSlot 34) i)) = empiricalExpectation source f := by
  simp only [Fintype.sum_option, childMass, point]
  rw [← Finset.mul_sum, slot_sum_map]
  simp only [empiricalExpectation, source_roots, source_degree, Multiset.map_add, Multiset.sum_add,
    Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.map_singleton, Multiset.sum_singleton, nsmul_eq_mul]
  rw [slots_card]
  norm_num
  ring

theorem source_centroid_zero : source.roots.sum=0 := by
  simp only [source_roots, Multiset.sum_add, Multiset.sum_nsmul, Multiset.sum_singleton,
    base_roots_sum, nsmul_zero, add_zero]

theorem source_variance : empiricalVariance source = 9/10 := by
  rw [empiricalVariance, source_centroid_zero, zero_div, ← source_root_law]
  simp only [Fintype.sum_option, childMass, point, sub_zero, norm_zero,
    zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
  simp only [rootSlot, slot_norm, one_pow, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [slots_card]
  norm_num

theorem finite_source_gini : finiteGini (childMass (1/10)) (point (rootSlot 34)) = empiricalGini source := by
  unfold empiricalGini
  rw [← source_root_law (fun x => empiricalExpectation source (fun y => ‖x-y‖))]
  unfold finiteGini
  apply Finset.sum_congr rfl
  intro i _
  rw [← source_root_law (fun y => ‖point (rootSlot 34) i-y‖), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem source_gini_formula : empiricalGini source = (81/100:ℝ)*empiricalGini (base 34)+9/50 := by
  rw [← finite_source_gini]
  have h := child_gini (rootSlot 34) (slot_norm 34) (1/10)
  have hg : finiteGini (fun _ : Slots 34 => 1/(Fintype.card (Slots 34):ℝ)) (rootSlot 34) = empiricalGini (base 34) := by
    simpa only [uniformGini, slots_card, Nat.cast_add, Nat.cast_ofNat] using uniformGini34_actual
  rw [h, hg]
  norm_num

theorem polygon_gini_lower : 4/Real.pi-Real.pi/(2*36^2) < empiricalGini (base 34) := by
  let x : ℝ := Real.pi/72
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : x < 1 := by dsimp [x]; linarith [Real.pi_lt_four]
  have hsq : x^2 < 1 := by nlinarith [mul_pos (sub_pos.mpr hx1) (by linarith : 0 < 1+x)]
  have hnum : 0 < 1-x^2/2 := by nlinarith
  have hsin := Real.sin_lt hx
  have hcos := Real.one_sub_sq_div_two_lt_cos hx.ne'
  have hquot : (1-x^2/2)/x < Real.cos x/Real.sin x := by
    apply (div_lt_div_iff₀ hx sin_half_angle_pos).mpr
    exact (mul_lt_mul_of_pos_left hsin hnum).trans (mul_lt_mul_of_pos_right hcos hx)
  calc
    4/Real.pi-Real.pi/(2*36^2) = (1/18:ℝ)*((1-x^2/2)/x) := by
      dsimp [x]
      field_simp [Real.pi_pos.ne']
      ring
    _ < (1/18:ℝ)*(Real.cos x/Real.sin x) := mul_lt_mul_of_pos_left hquot (by norm_num)
    _ = empiricalGini (base 34) := by rw [polygon_gini_exact]; dsimp [x]; ring

theorem circle_gini_violation : 4*Real.sqrt (empiricalVariance source)/Real.pi < empiricalGini source := by
  have hlow := mul_lt_mul_of_pos_left polygon_gini_lower (by norm_num : (0:ℝ) < 81/100)
  have hG : (81/100:ℝ)*(4/Real.pi-Real.pi/(2*36^2))+9/50 < empiricalGini source := by
    rw [source_gini_formula]
    linarith
  have hp := mul_lt_mul_of_pos_left hG Real.pi_pos
  have he : Real.pi*((81/100:ℝ)*(4/Real.pi-Real.pi/(2*36^2))+9/50) =
      81/25+(9/50:ℝ)*Real.pi-Real.pi^2/3200 := by
    field_simp [Real.pi_pos.ne']
    ring
  rw [he] at hp
  have hpisq : Real.pi^2 < 10 := by
    have hh := mul_pos (sub_pos.mpr Real.pi_lt_d2) (by linarith [Real.pi_pos] : 0 < 3.15+Real.pi)
    nlinarith
  have hmargin : (19/5:ℝ) < Real.pi*empiricalGini source := by
    nlinarith [Real.pi_gt_d2]
  have hs : Real.sqrt (empiricalVariance source) < 19/20 := by
    rw [source_variance]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 9/10), Real.sqrt_nonneg (9/10:ℝ)]
  apply (div_lt_iff₀ Real.pi_pos).mpr
  nlinarith

theorem normalized_gini_violation : 4/Real.pi < empiricalGini source/Real.sqrt (empiricalVariance source) := by
  have hs : 0 < Real.sqrt (empiricalVariance source) := Real.sqrt_pos.mpr (by rw [source_variance]; norm_num)
  apply (lt_div_iff₀ hs).mpr
  rw [show (4/Real.pi)*Real.sqrt (empiricalVariance source) =
    4*Real.sqrt (empiricalVariance source)/Real.pi by ring]
  exact circle_gini_violation

theorem source_roots_unit_disk (i : source.roots) : ‖(i:ℂ)‖ ≤ 1 := by
  have hi := (mem_roots source_monic.ne_zero).mp (Multiset.coe_mem (x := i))
  change source.eval (i:ℂ)=0 at hi
  simp only [source, base, eval_mul, eval_sub, eval_pow, eval_X, eval_one] at hi
  rcases mul_eq_zero.mp hi with h | h
  · have he : (i:ℂ)=0 := eq_zero_of_pow_eq_zero h
    simp [he]
  · have he : (i:ℂ)^36=1 := sub_eq_zero.mp h
    have hn := congrArg norm he
    simp only [norm_pow, norm_one] at hn
    have heq : ‖(i:ℂ)‖=1 := (pow_left_inj₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      (by norm_num : 36 ≠ 0)).mp (by simpa using hn)
    exact le_of_eq heq



end
end DerivativeChainGiniCircle


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily DerivativeChainDivisorAnchor DerivativeChainContinuation
open DerivativeChainGiniCircle




























theorem solution :
    _root_.DerivativeChainGiniCircle.source = (X^4*(X^36-1):ℂ[X]) ∧ _root_.DerivativeChainGiniCircle.source.Monic ∧ _root_.DerivativeChainGiniCircle.source.natDegree=40 ∧
    (∀ i : _root_.DerivativeChainGiniCircle.source.roots, ‖(i:ℂ)‖ ≤ 1) ∧ _root_.DerivativeChainGiniCircle.source.roots.sum=0 ∧
    (∀ f : ℂ → ℝ, (∑ i : Option (_root_.DerivativeChainGiniFamily.Slots 34), _root_.DerivativeChainGiniFamily.childMass (1/10) i*f (_root_.DerivativeChainGiniFamily.point (_root_.DerivativeChainGiniFamily.rootSlot 34) i)) = _root_.DerivativeChainGiniFamily.empiricalExpectation _root_.DerivativeChainGiniCircle.source f) ∧
    _root_.DerivativeChainGiniFamily.empiricalVariance _root_.DerivativeChainGiniCircle.source=9/10 ∧
    _root_.DerivativeChainGiniFamily.empiricalGini _root_.DerivativeChainGiniCircle.source=(81/100:ℝ)*((1/18:ℝ)*Real.cos (Real.pi/72)/Real.sin (Real.pi/72))+9/50 ∧
    4*Real.sqrt (_root_.DerivativeChainGiniFamily.empiricalVariance _root_.DerivativeChainGiniCircle.source)/Real.pi < _root_.DerivativeChainGiniFamily.empiricalGini _root_.DerivativeChainGiniCircle.source ∧
    4/Real.pi < _root_.DerivativeChainGiniFamily.empiricalGini _root_.DerivativeChainGiniCircle.source/Real.sqrt (_root_.DerivativeChainGiniFamily.empiricalVariance _root_.DerivativeChainGiniCircle.source) := by
  refine ⟨rfl, _root_.DerivativeChainGiniCircle.source_monic, _root_.DerivativeChainGiniCircle.source_degree, _root_.DerivativeChainGiniCircle.source_roots_unit_disk, _root_.DerivativeChainGiniCircle.source_centroid_zero,
    _root_.DerivativeChainGiniCircle.source_root_law, _root_.DerivativeChainGiniCircle.source_variance, ?_, _root_.DerivativeChainGiniCircle.circle_gini_violation, _root_.DerivativeChainGiniCircle.normalized_gini_violation⟩
  rw [_root_.DerivativeChainGiniCircle.source_gini_formula, _root_.DerivativeChainGiniCircle.polygon_gini_exact]
