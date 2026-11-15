-- Prove2me | solution 1 for CurrentAFT.RationalFullResponseProgram.matrix_error_eventually
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T21:22:20.434633+00:00
-- url     : https://prove2.me/submissions/c8dc8f90-d0f4-43e2-8e46-c941daadcfaa

import Definitions.Def_InfoLossLAR_NativeBundle_12
import Mathlib
import Theorems.Thm_AFT_FiniteDist_l1_prod_le
import Theorems.Thm_CurrentAFT_RationalBackgroundPopulationProgram_current_error
import Theorems.Thm_CurrentAFT_RationalFullResponseProgram_choiceAverage_bound
import Theorems.Thm_CurrentAFT_RationalPackedRootProgram_current_error_raw
namespace P2Mb608f3c5
end P2Mb608f3c5
section
namespace AFT.RationalNumerics
open scoped BigOperators
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h3 (value : ℝ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (index : ℕ) :
    |(-1 : ℝ)^index*value^(2*index+1)/(2*index+1 : ℕ)| ≤ (1/2 : ℝ)^(index+1) := by
  rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (pow_nonneg hv _),abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ value^(2*index+1) := div_le_self (pow_nonneg hv _) (by exact_mod_cast (show 1≤2*index+1 by omega))
    _ ≤ (1/2 : ℝ)^(2*index+1) := pow_le_pow_left₀ hv hv' _
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
open _root_.P2Mb608f3c5 renaming h3 → _p2mH3
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h2 (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (terms : ℕ) :
    |(_root_.AFT.RationalNumerics.arctanSum value terms : ℝ)-Real.arctan value| ≤ (1/2 : ℝ)^terms := by
  have hv0 : (0 : ℝ) ≤ value := by exact_mod_cast hv
  have hv1 : (value : ℝ) ≤ 1/2 := by
    have hh : value*2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hv'
    have hh' : (value : ℝ)*2 ≤ 1 := by exact_mod_cast hh
    linarith
  let term := fun index : ℕ => (-1 : ℝ)^index*(value : ℝ)^(2*index+1)/(2*index+1 : ℕ)
  have hseries : HasSum term (Real.arctan value) := Real.hasSum_arctan (by
    rw [Real.norm_eq_abs,abs_of_nonneg hv0]
    linarith)
  have hsplit := hseries.summable.sum_add_tsum_nat_add terms
  rw [hseries.tsum_eq] at hsplit
  have hcast : (_root_.AFT.RationalNumerics.arctanSum value terms : ℝ)=∑ i∈Finset.range terms,term i := by
    unfold _root_.AFT.RationalNumerics.arctanSum term
    push_cast
    rfl
  have hgeom : Summable (fun i : ℕ => (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i) :=
    (summable_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left _
  have hbound (i : ℕ) : ‖term (i+terms)‖ ≤ (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i := by
    have hh := _p2mH3 (value : ℝ) hv0 hv1 (i+terms)
    rw [← pow_add]
    have hi : i+terms+1=terms+1+i := by omega
    simpa only [term,Real.norm_eq_abs,hi] using hh
  have htail := (summable_nat_add_iff terms).mpr hseries.summable
  have hnorm := htail.norm
  have hsum := (norm_tsum_le_tsum_norm hnorm).trans (Summable.tsum_le_tsum hbound hnorm hgeom)
  have hgeomval : (∑' i : ℕ,(1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i)=(1/2 : ℝ)^terms := by
    have hh := ((hasSum_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left
      ((1/2 : ℝ)^(terms+1))).tsum_eq
    calc
      _ = (1/2 : ℝ)^(terms+1)*2 := by
        simpa only [show ((1 : ℝ)-1/2)⁻¹=2 by norm_num] using hh
      _ = _ := by rw [pow_succ]; ring
  rw [hgeomval,Real.norm_eq_abs] at hsum
  rw [hcast,abs_sub_comm,show Real.arctan (value : ℝ)-(∑ i∈Finset.range terms,term i)=
    ∑' i,term (i+terms) by linarith]
  exact hsum
open _root_.P2Mb608f3c5 renaming h2 → _p2mH2
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h11 (bits : ℕ) : |(_root_.AFT.RationalNumerics.piApprox bits : ℝ)-Real.pi| ≤ 1/(2 : ℝ)^bits := by
  have h1 := _p2mH2 (1/2) (by norm_num) (by norm_num) (bits+3)
  have h2 := _p2mH2 (1/3) (by norm_num) (by norm_num) (bits+3)
  have hid : Real.pi=4*(Real.arctan (1/2)+Real.arctan (1/3)) := by
    have hh := Real.arctan_inv_2_add_arctan_inv_3
    norm_num only [one_div] at ⊢
    linarith
  have he : (_root_.AFT.RationalNumerics.piApprox bits : ℝ)-Real.pi=4*((_root_.AFT.RationalNumerics.arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)+
      ((_root_.AFT.RationalNumerics.arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3))) := by
    rw [hid]
    simp only [_root_.AFT.RationalNumerics.piApprox,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add]
    ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    _ ≤ 4*(|(_root_.AFT.RationalNumerics.arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)|+
        |(_root_.AFT.RationalNumerics.arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3)|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ 4*((1/2 : ℝ)^(bits+3)+(1/2 : ℝ)^(bits+3)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using add_le_add h1 h2
    _ = _ := by rw [pow_add,div_pow,one_pow]; norm_num; ring
open _root_.P2Mb608f3c5 renaming h11 → _p2mH11
end
open _root_.P2Mb608f3c5 renaming h2 → _p2mH2
open _root_.P2Mb608f3c5 renaming h3 → _p2mH3
open _root_.P2Mb608f3c5 renaming h11 → _p2mH11
end AFT.RationalNumerics
open _root_.P2Mb608f3c5 renaming h2 → _p2mH2
open _root_.P2Mb608f3c5 renaming h3 → _p2mH3
open _root_.P2Mb608f3c5 renaming h11 → _p2mH11
end
open _root_.P2Mb608f3c5 renaming h2 → _p2mH2
open _root_.P2Mb608f3c5 renaming h3 → _p2mH3
open _root_.P2Mb608f3c5 renaming h11 → _p2mH11
namespace AFT
end AFT
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.piApprox
end AFT.RationalNumerics.piApprox
section
namespace AFT.RationalNumerics
open scoped BigOperators
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h6 (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2)
    (terms : ℕ) (ht : 0 < terms) :
    |(_root_.AFT.RationalNumerics.expSum value terms : ℝ)-Real.exp value| ≤ 2*(1/2 : ℝ)^terms := by
  have hv0 : (0 : ℝ) ≤ value := by exact_mod_cast hv
  have hv1 : (value : ℝ) ≤ 1/2 := by
    have hh : value*2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hv'
    have hh' : (value : ℝ)*2 ≤ 1 := by exact_mod_cast hh
    linarith
  have hterm : (1 : ℝ) ≤ terms := by exact_mod_cast ht
  have hfactorial : (1 : ℝ) ≤ terms.factorial := by exact_mod_cast Nat.factorial_pos terms
  have hden : (0 : ℝ) < (terms.factorial : ℝ)*terms := by positivity
  have hquot : ((terms+1 : ℕ) : ℝ)/((terms.factorial : ℝ)*terms) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    push_cast
    nlinarith
  have hh := Real.exp_bound (x := (value : ℝ)) (by rw [abs_of_nonneg hv0]; linarith) ht
  have he : (_root_.AFT.RationalNumerics.expSum value terms : ℝ)=∑ i∈Finset.range terms,(value : ℝ)^i/(i.factorial : ℕ) := by
    unfold _root_.AFT.RationalNumerics.expSum
    push_cast
    rfl
  rw [he,abs_sub_comm]
  apply hh.trans
  rw [abs_of_nonneg hv0]
  exact (mul_le_mul (pow_le_pow_left₀ hv0 hv1 terms) hquot (by positivity) (by positivity)).trans_eq (mul_comm _ _)
open _root_.P2Mb608f3c5 renaming h6 → _p2mH6
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h10 (first second : ℝ) (hf : 1 ≤ first) (hs : 1 ≤ second) :
    |first⁻¹-second⁻¹| ≤ |first-second| := by
  have hfirst : first ≠ 0 := by linarith
  have hsecond : second ≠ 0 := by linarith
  have he : first⁻¹-second⁻¹=(second-first)/(first*second) := by field_simp
  rw [he,abs_div,abs_sub_comm,abs_of_nonneg (by positivity : 0 ≤ first*second)]
  exact div_le_self (abs_nonneg _) (by nlinarith)
open _root_.P2Mb608f3c5 renaming h10 → _p2mH10
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h12 (first second : ℝ)
    (hf : 0 ≤ first ∧ first ≤ 1) (hs : 0 ≤ second ∧ second ≤ 1) (count : ℕ) :
    |first^count-second^count| ≤ (count : ℝ)*|first-second| := by
  have hh := abs_pow_sub_pow_le first second count
  rw [abs_of_nonneg hf.1,abs_of_nonneg hs.1] at hh
  have hp : max first second^(count-1) ≤ 1 := pow_le_one₀ (le_max_of_le_left hf.1) (max_le hf.2 hs.2)
  calc
    _ ≤ |first-second| *count*max first second^(count-1) := hh
    _ ≤ |first-second| *count*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring
open _root_.P2Mb608f3c5 renaming h12 → _p2mH12
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h5 (argument : ℚ) (scale bits : ℕ)
    (ha : 0 ≤ argument) (hscale : 0 < scale) (hbound : 2*argument ≤ (scale : ℚ)) :
    |(_root_.AFT.RationalNumerics.expNegScaled argument scale bits : ℝ)-Real.exp (-(argument : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let value : ℚ := argument/(scale : ℚ)
  let terms := bits+scale+1
  have hs0 : (0 : ℚ) < scale := by exact_mod_cast hscale
  have hv0 : 0 ≤ value := div_nonneg ha hs0.le
  have hv1 : value ≤ 1/2 := by
    apply (div_le_iff₀ hs0).mpr
    linarith
  have ht : 0 < terms := by dsimp [terms]; omega
  have hfirst := _root_.AFT.RationalNumerics.expSum_ge_one value hv0 terms ht
  have hsecond : (1 : ℝ) ≤ Real.exp (value : ℝ) := Real.one_le_exp_iff.mpr (by exact_mod_cast hv0)
  have hpi := _p2mH12 ((_root_.AFT.RationalNumerics.expSum value terms : ℝ)⁻¹) ((Real.exp (value : ℝ))⁻¹)
    ⟨by positivity,inv_le_one_of_one_le₀ hfirst⟩ ⟨by positivity,inv_le_one_of_one_le₀ hsecond⟩ scale
  have hi := _p2mH10 (_root_.AFT.RationalNumerics.expSum value terms) (Real.exp (value : ℝ)) hfirst hsecond
  have happrox := (hpi.trans (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg scale))).trans
    (mul_le_mul_of_nonneg_left (_p2mH6 value hv0 hv1 terms ht) (Nat.cast_nonneg scale))
  have hexp : (Real.exp (value : ℝ))⁻¹^scale=Real.exp (-(argument : ℝ)) := by
    rw [← Real.exp_neg,← Real.exp_nat_mul]
    congr 1
    dsimp [value]
    push_cast
    field_simp
  have hprogram : (_root_.AFT.RationalNumerics.expNegScaled argument scale bits : ℝ)=(_root_.AFT.RationalNumerics.expSum value terms : ℝ)⁻¹^scale := by
    simp only [_root_.AFT.RationalNumerics.expNegScaled,value,terms,Rat.cast_pow,Rat.cast_inv]
  rw [hprogram,← hexp]
  apply happrox.trans
  have hsbound : (scale : ℝ) ≤ (2 : ℝ)^scale := by exact_mod_cast (Nat.lt_two_pow_self (n:=scale)).le
  calc
    _ ≤ (2 : ℝ)^scale*(2*(1/2 : ℝ)^terms) := mul_le_mul_of_nonneg_right hsbound (by positivity)
    _ = _ := by
      dsimp [terms]
      rw [pow_add,pow_add,div_pow,one_pow,div_pow,one_pow]
      field_simp
open _root_.P2Mb608f3c5 renaming h5 → _p2mH5
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h4 (argument : ℚ) (bits : ℕ) :
    |(_root_.AFT.RationalNumerics.expNegApprox argument bits : ℝ)-Real.exp (-max (argument : ℝ) 0)| ≤ 1/(2 : ℝ)^bits := by
  have hb : 2*max argument 0 ≤ (_root_.AFT.RationalNumerics.expScale argument : ℚ) := by
    have hh := Nat.le_ceil (max argument 0)
    simp only [_root_.AFT.RationalNumerics.expScale,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    linarith
  have hh := _p2mH5 (max argument 0) (_root_.AFT.RationalNumerics.expScale argument) bits
    (le_max_right _ _) (_root_.AFT.RationalNumerics.expScale_positive argument) hb
  simpa only [_root_.AFT.RationalNumerics.expNegApprox,Rat.cast_max,Rat.cast_zero] using hh
open _root_.P2Mb608f3c5 renaming h4 → _p2mH4
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h7 (first second : ℝ) (hf : 0 ≤ first) (hs : 0 ≤ second) :
    |Real.exp (-first)-Real.exp (-second)| ≤ |first-second| := by
  have ordered (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      Real.exp (-a)-Real.exp (-b) ≤ b-a := by
    have he := Real.add_one_le_exp (a-b)
    have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-a)).le
    have heq : Real.exp (-a)*Real.exp (a-b)=Real.exp (-b) := by rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hm
    have hl : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hh := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hab)
    nlinarith
  rcases le_total first second with h|h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))),
      abs_of_nonpos (sub_nonpos.mpr h)]
    have hh := ordered first second hf h
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr (by linarith))),
      abs_of_nonneg (sub_nonneg.mpr h)]
    have hh := ordered second first hs h
    linarith
open _root_.P2Mb608f3c5 renaming h7 → _p2mH7
end
open _root_.P2Mb608f3c5 renaming h4 → _p2mH4
open _root_.P2Mb608f3c5 renaming h5 → _p2mH5
open _root_.P2Mb608f3c5 renaming h6 → _p2mH6
open _root_.P2Mb608f3c5 renaming h7 → _p2mH7
open _root_.P2Mb608f3c5 renaming h10 → _p2mH10
open _root_.P2Mb608f3c5 renaming h12 → _p2mH12
end AFT.RationalNumerics
open _root_.P2Mb608f3c5 renaming h4 → _p2mH4
open _root_.P2Mb608f3c5 renaming h5 → _p2mH5
open _root_.P2Mb608f3c5 renaming h6 → _p2mH6
open _root_.P2Mb608f3c5 renaming h7 → _p2mH7
open _root_.P2Mb608f3c5 renaming h10 → _p2mH10
open _root_.P2Mb608f3c5 renaming h12 → _p2mH12
end
open _root_.P2Mb608f3c5 renaming h4 → _p2mH4
open _root_.P2Mb608f3c5 renaming h5 → _p2mH5
open _root_.P2Mb608f3c5 renaming h6 → _p2mH6
open _root_.P2Mb608f3c5 renaming h7 → _p2mH7
open _root_.P2Mb608f3c5 renaming h10 → _p2mH10
open _root_.P2Mb608f3c5 renaming h12 → _p2mH12
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.independentCoordinates
end AFT.GaussianSource.independentCoordinates
namespace AFT.GaussianSource.independentCoordinates.match_1
end AFT.GaussianSource.independentCoordinates.match_1
namespace AFT.GaussianSource.integerGaussian
end AFT.GaussianSource.integerGaussian
namespace AFT.GaussianSource.latticeGaussian
end AFT.GaussianSource.latticeGaussian
namespace AFT.GaussianSource.latticeWeight
end AFT.GaussianSource.latticeWeight
namespace AFT.GaussianSource.residueGaussian
end AFT.GaussianSource.residueGaussian
namespace AFT.GaussianSource.weight
end AFT.GaussianSource.weight
namespace AFT.RationalNumerics.expNegApprox
end AFT.RationalNumerics.expNegApprox
namespace AFT.RationalNumerics.expNegScaled
end AFT.RationalNumerics.expNegScaled
namespace AFT.RationalNumerics.expScale
end AFT.RationalNumerics.expScale
namespace AFT.RationalNumerics.expSum
end AFT.RationalNumerics.expSum
section
namespace AFT.RationalNumerics
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h8 (squaredWidth : ℚ) (point : ℤ) (bits : ℕ)
    (hwidth : 0 < squaredWidth) :
    |(_root_.AFT.RationalNumerics.gaussianApprox squaredWidth point bits : ℝ)-
      Real.exp (-Real.pi*(point : ℝ)^2/(squaredWidth : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let ratio := _root_.AFT.RationalNumerics.gaussianRatio squaredWidth point
  let guard := _root_.AFT.RationalNumerics.gaussianGuard squaredWidth point
  let argument := _root_.AFT.RationalNumerics.piApprox (bits+guard+1)*ratio
  have hr0 : (0 : ℚ) ≤ ratio := div_nonneg (sq_nonneg _) hwidth.le
  have hr : (0 : ℝ) ≤ ratio := by exact_mod_cast hr0
  have hguard : (ratio : ℝ) ≤ (guard : ℝ) := by exact_mod_cast Nat.le_ceil ratio
  have hguardpow : (guard : ℝ) ≤ (2 : ℝ)^guard := by exact_mod_cast (Nat.lt_two_pow_self (n:=guard)).le
  have hpi := _p2mH11 (bits+guard+1)
  have harg : |(argument : ℝ)-Real.pi*(ratio : ℝ)| ≤ 1/(2 : ℝ)^(bits+1) := by
    have he : (argument : ℝ)-Real.pi*(ratio : ℝ)=((_root_.AFT.RationalNumerics.piApprox (bits+guard+1) : ℝ)-Real.pi)*(ratio : ℝ) := by
      dsimp [argument]
      push_cast
      ring
    rw [he,abs_mul,abs_of_nonneg hr]
    calc
      _ ≤ (1/(2 : ℝ)^(bits+guard+1))*(2 : ℝ)^guard :=
        mul_le_mul hpi (hguard.trans hguardpow) hr (by positivity)
      _ = _ := by rw [pow_add,pow_add,pow_add]; field_simp
  have ht : 0 ≤ Real.pi*(ratio : ℝ) := mul_nonneg Real.pi_pos.le hr
  have hclip : |max (argument : ℝ) 0-Real.pi*(ratio : ℝ)| ≤ 1/(2 : ℝ)^(bits+1) := by
    have hh := abs_max_sub_max_le_abs (argument : ℝ) (Real.pi*(ratio : ℝ)) 0
    rw [max_eq_left ht] at hh
    exact hh.trans harg
  have he := _p2mH4 argument (bits+1)
  have hl := _p2mH7 (max (argument : ℝ) 0) (Real.pi*(ratio : ℝ)) (le_max_right _ _) ht
  have htarget : -Real.pi*(point : ℝ)^2/(squaredWidth : ℝ) = -(Real.pi*(ratio : ℝ)) := by
    dsimp [ratio,_root_.AFT.RationalNumerics.gaussianRatio]
    push_cast
    ring
  rw [htarget]
  calc
    _ ≤ |(_root_.AFT.RationalNumerics.expNegApprox argument (bits+1) : ℝ)-Real.exp (-max (argument : ℝ) 0)|+
        |Real.exp (-max (argument : ℝ) 0)-Real.exp (-(Real.pi*(ratio : ℝ)))| := abs_sub_le _ _ _
    _ ≤ 1/(2 : ℝ)^(bits+1)+1/(2 : ℝ)^(bits+1) := add_le_add he (hl.trans hclip)
    _ = _ := by rw [pow_succ]; field_simp; norm_num
open _root_.P2Mb608f3c5 renaming h8 → _p2mH8
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h9 (squaredWidth : ℚ) (width : ℝ) (point : ℤ) (bits : ℕ)
    (hwidth : 0 < squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) :
    |(_root_.AFT.RationalNumerics.gaussianApprox squaredWidth point bits : ℝ)-_root_.AFT.GaussianSource.weight width point| ≤ 1/(2 : ℝ)^bits := by
  convert _p2mH8 squaredWidth point bits hwidth using 1
  unfold _root_.AFT.GaussianSource.weight
  rw [hsquare]
  have h : -(Real.pi / (squaredWidth : ℝ)) * (point : ℝ)^2 =
      -Real.pi * (point : ℝ)^2 / (squaredWidth : ℝ) := by ring
  rw [h]
open _root_.P2Mb608f3c5 renaming h9 → _p2mH9
end
open _root_.P2Mb608f3c5 renaming h8 → _p2mH8
open _root_.P2Mb608f3c5 renaming h9 → _p2mH9
end AFT.RationalNumerics
open _root_.P2Mb608f3c5 renaming h8 → _p2mH8
open _root_.P2Mb608f3c5 renaming h9 → _p2mH9
end
open _root_.P2Mb608f3c5 renaming h8 → _p2mH8
open _root_.P2Mb608f3c5 renaming h9 → _p2mH9
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.condition
end AFT.FiniteDist.condition
namespace AFT.FiniteDist.totalVariation
end AFT.FiniteDist.totalVariation
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.integerSum
end AFT.RootSlice.integerSum
namespace AFT.RootSlice.law
end AFT.RootSlice.law
namespace AFT.RootSlice.probability
end AFT.RootSlice.probability
section
namespace AFT.SignedConditioning
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h18 (first second : Color → ℝ) :
    |(∑ color, first color) - ∑ color, second color| ≤ ∑ color, |first color - second color| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _
open _root_.P2Mb608f3c5 renaming h18 → _p2mH18
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h19 (signed reference : Color → ℝ)
    (href : ∀ color, 0 ≤ reference color)
    (hsigned : 0 < ∑ color, signed color) (hreference : 0 < ∑ color, reference color) :
    (∑ color, |signed color / (∑ x, signed x) - reference color / (∑ x, reference x)|) ≤
      2 * (∑ color, |signed color - reference color|) / (∑ color, signed color) := by
  let total := ∑ color, signed color
  let referenceTotal := ∑ color, reference color
  let error := ∑ color, |signed color - reference color|
  have hmass : |referenceTotal - total| ≤ error := by
    simpa only [abs_sub_comm] using _p2mH18 signed reference
  have hpoint (color) : |signed color / total - reference color / referenceTotal| ≤
      |signed color - reference color| / total +
        reference color * |referenceTotal - total| / (total * referenceTotal) := by
    have heq : signed color / total - reference color / referenceTotal =
        (signed color - reference color) / total +
          reference color * (referenceTotal - total) / (total * referenceTotal) := by
      dsimp only [total, referenceTotal]
      field_simp
      ring
    rw [heq]
    exact (abs_add_le _ _).trans_eq (by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hsigned,
        abs_of_pos (mul_pos hsigned hreference), abs_of_nonneg (href color)])
  have hh := Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hpoint color)
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul] at hh
  have heq : (∑ color, |signed color - reference color|) / total +
      (∑ color, reference color) * |referenceTotal - total| / (total * referenceTotal) =
        (error + |referenceTotal - total|) / total := by
    dsimp only [error, total, referenceTotal]
    field_simp
  rw [heq] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hsigned.le
  linarith
open _root_.P2Mb608f3c5 renaming h19 → _p2mH19
end
open _root_.P2Mb608f3c5 renaming h18 → _p2mH18
open _root_.P2Mb608f3c5 renaming h19 → _p2mH19
end AFT.SignedConditioning
open _root_.P2Mb608f3c5 renaming h18 → _p2mH18
open _root_.P2Mb608f3c5 renaming h19 → _p2mH19
end
open _root_.P2Mb608f3c5 renaming h18 → _p2mH18
open _root_.P2Mb608f3c5 renaming h19 → _p2mH19
namespace AFT.FiniteConvolutionProgram
end AFT.FiniteConvolutionProgram
namespace AFT.FiniteConvolutionProgram.windowIndexEquiv
end AFT.FiniteConvolutionProgram.windowIndexEquiv
namespace AFT.RationalNumerics.gaussianApprox
end AFT.RationalNumerics.gaussianApprox
namespace AFT.RationalNumerics.gaussianRatio
end AFT.RationalNumerics.gaussianRatio
namespace AFT.SignedConditioning
end AFT.SignedConditioning
section
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h13 (squaredWidth : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hwidth : 0 < squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) :
    (∑ point,|(_root_.AFT.RationalNumerics.windowApproxLaw squaredWidth cutoff bits).weight point-
      (_root_.AFT.GaussianSource.windowGaussian width cutoff).weight point|) ≤ 1/(2 : ℝ)^bits := by
  let raw : _root_.AFT.GaussianSource.Window cutoff → ℝ := fun point => (_root_.AFT.RationalNumerics.windowApproxRaw squaredWidth cutoff bits point : ℝ)
  have hraw : 1 ≤ ∑ point,raw point := by
    have hh := _root_.AFT.RationalNumerics.windowApproxNormalizer_ge_one squaredWidth cutoff bits
    rw [_root_.AFT.RationalNumerics.windowApproxNormalizer_eq_sum] at hh
    dsimp only [raw]
    exact_mod_cast hh
  have hnormal := _p2mH19 raw (fun point => _root_.AFT.GaussianSource.weight width point)
    (fun point => (_root_.AFT.GaussianSource.weight_pos _ _).le) (zero_lt_one.trans_le hraw)
    (zero_lt_one.trans_le (_root_.AFT.GaussianSource.windowNormalizer_ge_one width cutoff))
  have herr : (∑ point,|raw point-_root_.AFT.GaussianSource.weight width point|) ≤
      (2*cutoff+1 : ℕ)/(2 : ℝ)^(_root_.AFT.RationalNumerics.windowApproxPrecision cutoff bits) := by
    have hh := Finset.sum_le_sum (fun point (_ : point ∈ (Finset.univ : Finset (_root_.AFT.GaussianSource.Window cutoff))) =>
      _p2mH9 squaredWidth width point (_root_.AFT.RationalNumerics.windowApproxPrecision cutoff bits) hwidth hsquare)
    have hc : Fintype.card (_root_.AFT.GaussianSource.Window cutoff)=2*cutoff+1 := by
      rw [← Fintype.card_congr (_root_.AFT.FiniteConvolutionProgram.windowIndexEquiv cutoff),Fintype.card_fin]
    simpa only [raw,_root_.AFT.RationalNumerics.windowApproxRaw,Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul,mul_one_div] using hh
  have hden : 0 ≤ ∑ point,|raw point-_root_.AFT.GaussianSource.weight width point| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have heq : (∑ point,|(_root_.AFT.RationalNumerics.windowApproxLaw squaredWidth cutoff bits).weight point-
      (_root_.AFT.GaussianSource.windowGaussian width cutoff).weight point|)=
      ∑ point,|raw point/(∑ x,raw x)-_root_.AFT.GaussianSource.weight width point/(∑ x:_root_.AFT.GaussianSource.Window cutoff,_root_.AFT.GaussianSource.weight width x)| := by
    apply Finset.sum_congr rfl
    intro point _
    simp only [_root_.AFT.RationalNumerics.windowApproxLaw,_root_.AFT.RationalNumerics.windowApproxWeight,_root_.AFT.RationalNumerics.windowApproxNormalizer_eq_sum,_root_.AFT.GaussianSource.windowGaussian,_root_.AFT.FiniteDist.normalize,raw,Rat.cast_div,Rat.cast_sum]
  rw [heq]
  calc
    _ ≤ 2*(∑ point,|raw point-_root_.AFT.GaussianSource.weight width point|)/(∑ x,raw x) := hnormal
    _ ≤ 2*(∑ point,|raw point-_root_.AFT.GaussianSource.weight width point|)/1 :=
      div_le_div_of_nonneg_left (by positivity) zero_lt_one hraw
    _ ≤ 2*((2*cutoff+1 : ℕ)/(2 : ℝ)^(_root_.AFT.RationalNumerics.windowApproxPrecision cutoff bits)) := by rw [div_one]; gcongr
    _ ≤ 2*((2 : ℝ)^(2*cutoff+1)/(2 : ℝ)^(_root_.AFT.RationalNumerics.windowApproxPrecision cutoff bits)) := by
      gcongr
      exact_mod_cast (Nat.lt_two_pow_self (n:=2*cutoff+1)).le
    _ = _ := by
      unfold _root_.AFT.RationalNumerics.windowApproxPrecision
      rw [pow_add,pow_add]
      field_simp
      ring
open _root_.P2Mb608f3c5 renaming h13 → _p2mH13
end
open _root_.P2Mb608f3c5 renaming h13 → _p2mH13
end AFT.RationalNumerics
open _root_.P2Mb608f3c5 renaming h13 → _p2mH13
end
open _root_.P2Mb608f3c5 renaming h13 → _p2mH13
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.inputIteration
end AFT.MixedKernel.inputIteration
section
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h1 (kernel : (Slot → Color) → ℝ) :
    kernel = ∑ point : Slot → Color, kernel point •
      _root_.AFT.MixedKernel.productKernel (fun slot color => if color = point slot then 1 else 0) := by
  funext word
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, _root_.AFT.MixedKernel.productKernel]
  have heq (point : Slot → Color) :
      (∏ slot : Slot, if word slot = point slot then (1 : ℝ) else 0) = if word = point then 1 else 0 := by
    by_cases hp : word = point
    · simp [hp]
    · have hd : ∃ slot, word slot ≠ point slot := by
        by_contra hn
        push_neg at hn
        exact hp (funext hn)
      obtain ⟨slot, hs⟩ := hd
      rw [if_neg hp]
      exact Finset.prod_eq_zero (Finset.mem_univ slot) (if_neg hs)
  simp only [heq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
open _root_.P2Mb608f3c5 renaming h1 → _p2mH1
end
open _root_.P2Mb608f3c5 renaming h1 → _p2mH1
end AFT.MixedKernel
open _root_.P2Mb608f3c5 renaming h1 → _p2mH1
end
open _root_.P2Mb608f3c5 renaming h1 → _p2mH1
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualBodyShiftProgram
end AFT.V7Calibration.actualBodyShiftProgram
namespace AFT.V7Calibration.actualLegWindowEquiv
end AFT.V7Calibration.actualLegWindowEquiv
namespace AFT.V7Calibration.actualPairSourceApproxLaw
end AFT.V7Calibration.actualPairSourceApproxLaw
namespace AFT.V7Calibration.actualPairSourceProgram
end AFT.V7Calibration.actualPairSourceProgram
namespace AFT.V7Calibration.rational_expectation_error
end AFT.V7Calibration.rational_expectation_error
section
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators
noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] _root_.AFT.V7Calibration.sliceProgramFinDecEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h21 (modulus boundary shift color : ℤ) :
    |(_root_.AFT.V7Calibration.sliceProbabilityProgram modulus boundary shift color : ℝ)|≤1 := by
  rw [_root_.AFT.V7Calibration.sliceProbabilityProgram_eq_original]
  split_ifs with hh
  · simp only [Rat.cast_inv,Rat.cast_natCast]
    rw [abs_of_nonneg (by positivity)]
    apply inv_le_one_of_one_le₀
    exact_mod_cast (Finset.one_le_card.mpr ⟨color,hh⟩)
  · norm_num
open _root_.P2Mb608f3c5 renaming h21 → _p2mH21
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h20 (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    |(_root_.AFT.V7Calibration.averagedSliceProgram modulus boundary start source width color : ℝ)|≤1 := by
  by_cases hw : width=0
  · subst width
    simp [_root_.AFT.V7Calibration.averagedSliceProgram_eq_sum,_root_.AFT.anchorInterval]
  simp only [_root_.AFT.V7Calibration.averagedSliceProgram_eq_sum,Rat.cast_sum,Rat.cast_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ shift∈_root_.AFT.anchorInterval start width,_root_.AFT.intervalAnchorLaw start width shift := by
      apply Finset.sum_le_sum
      intro shift _
      rw [abs_mul,_root_.AFT.V7Calibration.intervalProbabilityProgram_cast,abs_of_nonneg (_root_.AFT.intervalAnchorLaw_nonneg _ _ _)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (_p2mH21 modulus boundary (shift-source) color)
        (_root_.AFT.intervalAnchorLaw_nonneg start shift width)
    _ = 1 := _root_.AFT.intervalAnchorLaw_mass start width hw
open _root_.P2Mb608f3c5 renaming h20 → _p2mH20
end
open _root_.P2Mb608f3c5 renaming h20 → _p2mH20
open _root_.P2Mb608f3c5 renaming h21 → _p2mH21
end AFT.V7Calibration
open _root_.P2Mb608f3c5 renaming h20 → _p2mH20
open _root_.P2Mb608f3c5 renaming h21 → _p2mH21
end
open _root_.P2Mb608f3c5 renaming h20 → _p2mH20
open _root_.P2Mb608f3c5 renaming h21 → _p2mH21
namespace AFT.FiniteDist.dependentPairsEquiv
end AFT.FiniteDist.dependentPairsEquiv
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TensorChannel.applyLinear
end AFT.TensorChannel.applyLinear
namespace AFT.TensorChannel.center
end AFT.TensorChannel.center
section
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Output : Type*} [Fintype Index] [DecidableEq Index]
  {Old : Index → Type*} [∀ i, Fintype (Old i)]
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h16
    (law : ∀ i, _root_.AFT.FiniteDist (Old i)) (kernel : ((i : Index) → Old i) → ℝ)
    (slot : Index)
    (hc : ∀ tail : (i : {i // i ≠ slot}) → Old i.val,
      ∑ color, (law slot).weight color *
        kernel ((Equiv.piSplitAt slot Old).symm (color,tail)) = 0)
    (polynomial : ((i : Index) → Old i) → _root_.AFT.RepresentedPolynomial.Table Output)
    (hp : ∀ first second, (∀ i, i ≠ slot → first i = second i) →
      polynomial first = polynomial second) :
    (∑ word, MvPolynomial.C ((law slot).weight (word slot) * kernel word) * polynomial word) = 0 := by
  classical
  by_cases hn : Nonempty (Old slot)
  · let color₀ : Old slot := Classical.choice hn
    rw [← (Equiv.piSplitAt slot Old).symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro tail _
    have he (color : Old slot) : polynomial ((Equiv.piSplitAt slot Old).symm (color,tail)) =
        polynomial ((Equiv.piSplitAt slot Old).symm (color₀,tail)) := by
      apply hp
      intro other ho
      simp [Equiv.piSplitAt,ho]
    simp only [he]
    have hv (color : Old slot) : (Equiv.piSplitAt slot Old).symm (color,tail) slot = color := by
      simp [Equiv.piSplitAt]
    simp only [hv]
    rw [← Finset.sum_mul, ← map_sum, hc, map_zero, zero_mul]
  · haveI : IsEmpty (Old slot) := not_nonempty_iff.mp hn
    haveI : IsEmpty ((i : Index) → Old i) := ⟨fun word => isEmptyElim (word slot)⟩
    simp
open _root_.P2Mb608f3c5 renaming h16 → _p2mH16
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h15
    (law : ∀ i, _root_.AFT.FiniteDist (Old i)) (forms : ∀ i, Old i → _root_.AFT.RepresentedPolynomial.Table Output)
    (kernel : ((i : Index) → Old i) → ℝ) (slot : Index) (constant : _root_.AFT.RepresentedPolynomial.Table Output)
    (hc : ∀ tail : (i : {i // i ≠ slot}) → Old i.val,
      ∑ color, (law slot).weight color *
        kernel ((Equiv.piSplitAt slot Old).symm (color,tail)) = 0) :
    _root_.AFT.RepresentedPolynomial.dependentPolynomial (Function.update forms slot
      (fun color => forms slot color + MvPolynomial.C ((law slot).weight color)*constant)) kernel =
      _root_.AFT.RepresentedPolynomial.dependentPolynomial forms kernel := by
  classical
  let remaining := fun word : (i : Index) → Old i =>
    ∏ other ∈ Finset.univ.erase slot, forms other (word other)
  have hz := _p2mH16 law kernel slot hc remaining (by
    intro first second h
    apply Finset.prod_congr rfl
    intro other ho
    rw [h other (Finset.mem_erase.mp ho).1])
  have hu (word : (i : Index) → Old i) :
      (fun other => Function.update forms slot
        (fun color => forms slot color + MvPolynomial.C ((law slot).weight color)*constant) other (word other)) =
      Function.update (fun other => forms other (word other)) slot
        (forms slot (word slot)+MvPolynomial.C ((law slot).weight (word slot))*constant) := by
    funext other
    by_cases ho : other=slot
    · subst other; simp
    · simp [Function.update_of_ne ho]
  have he : _root_.AFT.RepresentedPolynomial.dependentPolynomial (Function.update forms slot
      (fun color => forms slot color + MvPolynomial.C ((law slot).weight color)*constant)) kernel =
      _root_.AFT.RepresentedPolynomial.dependentPolynomial forms kernel + constant *
        (∑ word, MvPolynomial.C ((law slot).weight (word slot)*kernel word)*remaining word) := by
    unfold _root_.AFT.RepresentedPolynomial.dependentPolynomial
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro word _
    rw [hu,Finset.prod_update_of_mem (Finset.mem_univ slot),
      ← Finset.mul_prod_erase Finset.univ (fun other => forms other (word other)) (Finset.mem_univ slot)]
    simp only [Finset.sdiff_singleton_eq_erase,map_mul]
    dsimp only [remaining]
    ring
  rw [he,hz,mul_zero,add_zero]
open _root_.P2Mb608f3c5 renaming h15 → _p2mH15
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h14
    (law : ∀ i, _root_.AFT.FiniteDist (Old i)) (forms : ∀ i, Old i → _root_.AFT.RepresentedPolynomial.Table Output)
    (constants : Index → _root_.AFT.RepresentedPolynomial.Table Output) (kernel : ((i : Index) → Old i) → ℝ)
    (selected : Finset Index)
    (hc : ∀ slot ∈ selected, ∀ tail : (i : {i // i ≠ slot}) → Old i.val,
      ∑ color, (law slot).weight color *
        kernel ((Equiv.piSplitAt slot Old).symm (color,tail)) = 0) :
    _root_.AFT.RepresentedPolynomial.dependentPolynomial (fun slot color => forms slot color -
      if slot ∈ selected then MvPolynomial.C ((law slot).weight color)*constants slot else 0) kernel =
      _root_.AFT.RepresentedPolynomial.dependentPolynomial forms kernel := by
  classical
  induction selected using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty,if_false,sub_zero]
  | @insert slot selected hs ih =>
    let previous : ∀ i, Old i → _root_.AFT.RepresentedPolynomial.Table Output := fun other color => forms other color -
      if other ∈ selected then MvPolynomial.C ((law other).weight color)*constants other else 0
    have he : (fun other color => forms other color -
        if other ∈ insert slot selected then MvPolynomial.C ((law other).weight color)*constants other else 0) =
        Function.update previous slot
          (fun color => previous slot color+MvPolynomial.C ((law slot).weight color)*(-constants slot)) := by
      funext other color
      by_cases ho : other=slot
      · subst other; simp [previous,hs,sub_eq_add_neg]
      · simp [previous,ho]
    rw [he,_p2mH15 law previous kernel slot (-constants slot)
      (hc slot (Finset.mem_insert_self _ _))]
    exact ih (fun other ho => hc other (Finset.mem_insert_of_mem ho))
open _root_.P2Mb608f3c5 renaming h14 → _p2mH14
set_option maxRecDepth 8192
omit [Fintype Index] in
theorem _root_.P2Mb608f3c5.h17
    (law : ∀ i, _root_.AFT.FiniteDist (Old i)) (kernel : ((i : Index) → Old i) → ℝ)
    (slot : Index)
    (hc : ∀ word, ∑ color, (law slot).weight color *
      kernel (Function.update word slot color) = 0)
    (tail : (i : {i // i ≠ slot}) → Old i.val) :
    ∑ color, (law slot).weight color *
      kernel ((Equiv.piSplitAt slot Old).symm (color,tail)) = 0 := by
  classical
  by_cases hn : Nonempty (Old slot)
  · let color₀ : Old slot := Classical.choice hn
    have he (color : Old slot) :
        Function.update ((Equiv.piSplitAt slot Old).symm (color₀,tail)) slot color =
          (Equiv.piSplitAt slot Old).symm (color,tail) := by
      funext other
      by_cases ho : other=slot
      · subst other; simp [Equiv.piSplitAt]
      · simp [Equiv.piSplitAt,ho]
    simpa only [he] using hc ((Equiv.piSplitAt slot Old).symm (color₀,tail))
  · haveI : IsEmpty (Old slot) := not_nonempty_iff.mp hn
    simp
open _root_.P2Mb608f3c5 renaming h17 → _p2mH17
end
open _root_.P2Mb608f3c5 renaming h14 → _p2mH14
open _root_.P2Mb608f3c5 renaming h15 → _p2mH15
open _root_.P2Mb608f3c5 renaming h16 → _p2mH16
open _root_.P2Mb608f3c5 renaming h17 → _p2mH17
end AFT.RepresentedPolynomial
open _root_.P2Mb608f3c5 renaming h14 → _p2mH14
open _root_.P2Mb608f3c5 renaming h15 → _p2mH15
open _root_.P2Mb608f3c5 renaming h16 → _p2mH16
open _root_.P2Mb608f3c5 renaming h17 → _p2mH17
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Root Old Output : Type*} [Fintype Old]
end
end AFT.RepresentedPolynomial
end
open _root_.P2Mb608f3c5 renaming h14 → _p2mH14
open _root_.P2Mb608f3c5 renaming h15 → _p2mH15
open _root_.P2Mb608f3c5 renaming h16 → _p2mH16
open _root_.P2Mb608f3c5 renaming h17 → _p2mH17
namespace AFT.MixedKernel.densityConjugate
end AFT.MixedKernel.densityConjugate
namespace AFT.MixedKernel.productKernel
end AFT.MixedKernel.productKernel
namespace AFT.RepresentedPolynomial.conditionalOldCenter
end AFT.RepresentedPolynomial.conditionalOldCenter
namespace AFT.RepresentedPolynomial.dependentPolynomial
end AFT.RepresentedPolynomial.dependentPolynomial
section
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h0 (reference : Slot → _root_.AFT.FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (hc : _root_.AFT.Hoeffding.Canonical reference Finset.univ kernel)
    (word : Slot → Color) :
    (∑ point,kernel point*_root_.AFT.MixedKernel.canonicalPointBasis reference point word)=kernel word := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  have hh := _p2mH14 (Output:=Unit)
    reference (fun slot color => MvPolynomial.C (R:=ℝ) (if word slot=color then 1 else 0))
    (fun _ => 1) kernel Finset.univ (by
      intro slot _ tail
      exact _p2mH17 reference kernel slot
        (hc.2 slot (Finset.mem_univ slot)) tail)
  simp only [Finset.mem_univ,if_true,mul_one,_root_.AFT.RepresentedPolynomial.dependentPolynomial,
    ←map_sub,←map_prod,←map_mul,←map_sum] at hh
  have he := MvPolynomial.C_injective Unit ℝ hh
  have hx := congrFun (_p2mH1 kernel) word
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,_root_.AFT.MixedKernel.productKernel] at hx
  exact he.trans hx.symm
open _root_.P2Mb608f3c5 renaming h0 → _p2mH0
end
open _root_.P2Mb608f3c5 renaming h0 → _p2mH0
end AFT.MixedKernel
open _root_.P2Mb608f3c5 renaming h0 → _p2mH0
end
open _root_.P2Mb608f3c5 renaming h0 → _p2mH0
namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.ControlCoordinates
end CurrentAFT.ControlCoordinates
namespace CurrentAFT.ControlCoordinates.centerBodySlot
end CurrentAFT.ControlCoordinates.centerBodySlot
namespace CurrentAFT.ControlCoordinates.centerPrimarySlot
end CurrentAFT.ControlCoordinates.centerPrimarySlot
namespace CurrentAFT.ControlCoordinates.coefficientStatistic
end CurrentAFT.ControlCoordinates.coefficientStatistic
namespace CurrentAFT.ControlCoordinates.kernelMean
end CurrentAFT.ControlCoordinates.kernelMean
namespace CurrentAFT.ControlCoordinates.pairedLift
end CurrentAFT.ControlCoordinates.pairedLift
namespace CurrentAFT.ControlCoordinates.twoPoolUStatistic
end CurrentAFT.ControlCoordinates.twoPoolUStatistic
section
namespace CurrentAFT.ControlProduct
open AFT ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ControlProduct.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ControlProduct.classicalSumDecidableEq
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
section SlotSpaces
variable {PS BS PT BT : Type*} [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT]
variable {PU BU : Type*} [Fintype PU] [Fintype BU]
end SlotSpaces
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h40 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    {r s r' s' : ℕ} (first : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r s)
    (second : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r' s')
    (colors : Fin (r + r') → Primary) (centers : Fin (s + s') → Body) :
    (_root_.CurrentAFT.ControlProduct.homogeneousProduct primary body first second).val colors centers =
      ((r + r').factorial : ℝ)⁻¹ * ((s + s').factorial : ℝ)⁻¹ *
        ∑ primaryOrder : Equiv.Perm (Fin (r + r')), ∑ bodyOrder : Equiv.Perm (Fin (s + s')),
          _root_.CurrentAFT.ControlProduct.finDisjointTensor first.val second.val (colors ∘ primaryOrder) (centers ∘ bodyOrder) := by
  exact (_root_.CurrentAFT.ControlProduct.symmetrize_apply (_root_.CurrentAFT.ControlProduct.finDisjointTensor first.val second.val) colors centers).trans (by
    simp only [Fintype.card_perm, Fintype.card_fin])
open _root_.P2Mb608f3c5 renaming h40 → _p2mH40
end
open _root_.P2Mb608f3c5 renaming h40 → _p2mH40
end CurrentAFT.ControlProduct
open _root_.P2Mb608f3c5 renaming h40 → _p2mH40
end
open _root_.P2Mb608f3c5 renaming h40 → _p2mH40
namespace CurrentAFT.ControlProduct
end CurrentAFT.ControlProduct
namespace CurrentAFT.ControlProduct.homogeneousProduct
end CurrentAFT.ControlProduct.homogeneousProduct
namespace CurrentAFT.GradedControlAlgebra
end CurrentAFT.GradedControlAlgebra
namespace CurrentAFT.GradedControlAlgebra.coefficientsToFamily
end CurrentAFT.GradedControlAlgebra.coefficientsToFamily
namespace CurrentAFT.GradedControlAlgebra.familyProduct
end CurrentAFT.GradedControlAlgebra.familyProduct
namespace CurrentAFT.GradedControlAlgebra.positiveArity
end CurrentAFT.GradedControlAlgebra.positiveArity
namespace CurrentAFT.GradedControlAlgebra.scalarAt
end CurrentAFT.GradedControlAlgebra.scalarAt
namespace CurrentAFT.GradedControlAlgebra.scalarKernel
end CurrentAFT.GradedControlAlgebra.scalarKernel
namespace CurrentAFT.GradedControlAlgebra.transportKernel
end CurrentAFT.GradedControlAlgebra.transportKernel
namespace CurrentAFT.GradedControlAlgebra.zeroArity
end CurrentAFT.GradedControlAlgebra.zeroArity
section
namespace CurrentAFT.GradedInverse
open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h64 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (order : ℕ) (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order)
    (hfirst : _root_.CurrentAFT.GradedInverse.VanishesBelow primary body order 1 family) (power : ℕ) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow primary body order power (family ^ power) := by
  induction power with
  | zero => exact _root_.CurrentAFT.GradedInverse.vanishesBelow_zero primary body order _
  | succ power ih =>
    rw [pow_succ]
    exact _root_.CurrentAFT.GradedInverse.vanishesBelow_mul primary body order power 1 _ family ih hfirst
open _root_.P2Mb608f3c5 renaming h64 → _p2mH64
end
open _root_.P2Mb608f3c5 renaming h64 → _p2mH64
end CurrentAFT.GradedInverse
open _root_.P2Mb608f3c5 renaming h64 → _p2mH64
end
open _root_.P2Mb608f3c5 renaming h64 → _p2mH64
namespace CurrentAFT.ControlProduct.disjointTensor
end CurrentAFT.ControlProduct.disjointTensor
namespace CurrentAFT.ControlProduct.finBlockSwap
end CurrentAFT.ControlProduct.finBlockSwap
namespace CurrentAFT.ControlProduct.finDisjointTensor
end CurrentAFT.ControlProduct.finDisjointTensor
namespace CurrentAFT.ControlProduct.finLeftUnit
end CurrentAFT.ControlProduct.finLeftUnit
namespace CurrentAFT.ControlProduct.finRightUnit
end CurrentAFT.ControlProduct.finRightUnit
namespace CurrentAFT.ControlProduct.reindexKernel
end CurrentAFT.ControlProduct.reindexKernel
namespace CurrentAFT.ControlProduct.scalarUnit
end CurrentAFT.ControlProduct.scalarUnit
namespace CurrentAFT.ControlProduct.symmetrize
end CurrentAFT.ControlProduct.symmetrize
namespace CurrentAFT.ControlProduct.truncatedHomogeneousProduct
end CurrentAFT.ControlProduct.truncatedHomogeneousProduct
section
namespace CurrentAFT.CanonicalReconstruction
open AFT ControlCoordinates ControlProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.CanonicalReconstruction.classicalFinDecidableEq
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h32 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    {r s : ℕ} (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r s)
    (colors : Fin r → Primary) (centers : Fin s → Body) :
    (∑ sourcePrimary, ∑ sourceBody,
      kernel.val sourcePrimary sourceBody *
        _root_.AFT.MixedKernel.canonicalPointBasis (fun _ : Fin r => primary) sourcePrimary colors *
          _root_.AFT.MixedKernel.canonicalPointBasis (fun _ : Fin s => body) sourceBody centers) =
      kernel.val colors centers := by
  have hprimary (fixed : Fin s → Body) :
      _root_.AFT.Hoeffding.Canonical (fun _ : Fin r => primary) Finset.univ (fun word => kernel.val word fixed) := by
    constructor
    · intro first second hequal
      have hword : first = second := funext fun index => hequal index (Finset.mem_univ index)
      rw [hword]
    · intro index _ word
      exact kernel.property.1 index word fixed
  have hbody (fixed : Fin r → Primary) :
      _root_.AFT.Hoeffding.Canonical (fun _ : Fin s => body) Finset.univ (kernel.val fixed) := by
    constructor
    · intro first second hequal
      have hword : first = second := funext fun index => hequal index (Finset.mem_univ index)
      rw [hword]
    · intro index _ word
      exact kernel.property.2.1 index fixed word
  have hp := _p2mH0 (fun _ : Fin r => primary)
    (fun word => kernel.val word centers) (hprimary centers) colors
  have hb (source : Fin r → Primary) := _p2mH0
    (fun _ : Fin s => body) (kernel.val source) (hbody source) centers
  calc
    _ = ∑ sourcePrimary,
        (∑ sourceBody, kernel.val sourcePrimary sourceBody *
          _root_.AFT.MixedKernel.canonicalPointBasis (fun _ : Fin s => body) sourceBody centers) *
          _root_.AFT.MixedKernel.canonicalPointBasis (fun _ : Fin r => primary) sourcePrimary colors := by
      apply Finset.sum_congr rfl
      intro source _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro other _
      ring
    _ = _ := by simp only [hb]; exact hp
open _root_.P2Mb608f3c5 renaming h32 → _p2mH32
set_option maxRecDepth 8192
private theorem _root_.P2Mb608f3c5.h209 {Color : Type*} [Fintype Color] (law : _root_.AFT.FiniteDist Color)
    (hpositive : ∀ color, 0 < law.weight color) (source output : Color) :
    law.weight source * _root_.AFT.Hoeffding.centeredAtom law source output =
      (if output = source then 1 else 0) - law.weight source := by
  by_cases hequal : source = output
  · subst output
    simp only [_root_.AFT.Hoeffding.centeredAtom, if_true, mul_sub, mul_one,
      mul_inv_cancel₀ (hpositive source).ne']
  · simp only [_root_.AFT.Hoeffding.centeredAtom, hequal, Ne.symm hequal, if_false, zero_sub, mul_neg, mul_one]
open _root_.P2Mb608f3c5 renaming h209 → _p2mH209
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h35 {Color : Type*} [Fintype Color] (law : _root_.AFT.FiniteDist Color)
    (hpositive : ∀ color, 0 < law.weight color) {Index : Type*} [Fintype Index] [DecidableEq Index]
    (source output : Index → Color) :
    (∏ index, law.weight (source index)) *
        (∏ index, _root_.AFT.Hoeffding.centeredAtom law (source index) (output index)) =
      _root_.AFT.MixedKernel.canonicalPointBasis (fun _ : Index => law) source output := by
  rw [← Finset.prod_mul_distrib]
  simp only [_p2mH209 law hpositive, _root_.AFT.MixedKernel.canonicalPointBasis]
open _root_.P2Mb608f3c5 renaming h35 → _p2mH35
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h34 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ color, 0 < body.weight color)
    {r s : ℕ} (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r s)
    (colors : Fin r → Primary) (centers : Fin s → Body) :
    (∑ sourcePrimary, ∑ sourceBody,
      ((∏ index, primary.weight (sourcePrimary index)) *
        (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) *
          _root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body sourcePrimary sourceBody colors centers) =
      kernel.val colors centers := by
  rw [← _p2mH32 primary body kernel colors centers]
  apply Finset.sum_congr rfl
  intro sourcePrimary _
  apply Finset.sum_congr rfl
  intro sourceBody _
  rw [← _p2mH35 primary hprimary, ← _p2mH35 body hbody]
  unfold _root_.CurrentAFT.CanonicalReconstruction.pointTensor
  ring
open _root_.P2Mb608f3c5 renaming h34 → _p2mH34
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h33 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ color, 0 < body.weight color)
    {r s : ℕ} (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r s) :
    (∑ sourcePrimary, ∑ sourceBody,
      ((∏ index, primary.weight (sourcePrimary index)) *
        (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
          _root_.CurrentAFT.CanonicalReconstruction.pointKernel primary body hprimary hbody sourcePrimary sourceBody) = kernel := by
  have hraw : (∑ sourcePrimary, ∑ sourceBody,
      ((∏ index, primary.weight (sourcePrimary index)) *
        (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
          _root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body sourcePrimary sourceBody) = kernel.val := by
    funext colors centers
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact _p2mH34 primary body hprimary hbody kernel colors centers
  have hsymmetric : _root_.CurrentAFT.ControlProduct.symmetrize kernel.val = kernel.val :=
    _root_.CurrentAFT.ControlProduct.symmetrize_of_symmetric kernel.val kernel.property.2.2
  have h := congrArg (_root_.CurrentAFT.ControlProduct.symmetrizeLinear (Primary := Primary) (Body := Body)) hraw
  simp only [map_sum, map_smul] at h
  change (∑ sourcePrimary, ∑ sourceBody,
      ((∏ index, primary.weight (sourcePrimary index)) *
        (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
          _root_.CurrentAFT.ControlProduct.symmetrize (_root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body sourcePrimary sourceBody)) = _root_.CurrentAFT.ControlProduct.symmetrize kernel.val at h
  rw [hsymmetric] at h
  apply Subtype.ext
  simpa only [Submodule.coe_sum, Submodule.coe_smul, _root_.CurrentAFT.CanonicalReconstruction.pointKernel] using h
open _root_.P2Mb608f3c5 renaming h33 → _p2mH33
end
open _root_.P2Mb608f3c5 renaming h32 → _p2mH32
open _root_.P2Mb608f3c5 renaming h33 → _p2mH33
open _root_.P2Mb608f3c5 renaming h34 → _p2mH34
open _root_.P2Mb608f3c5 renaming h35 → _p2mH35
open _root_.P2Mb608f3c5 renaming h209 → _p2mH209
end CurrentAFT.CanonicalReconstruction
open _root_.P2Mb608f3c5 renaming h32 → _p2mH32
open _root_.P2Mb608f3c5 renaming h33 → _p2mH33
open _root_.P2Mb608f3c5 renaming h34 → _p2mH34
open _root_.P2Mb608f3c5 renaming h35 → _p2mH35
open _root_.P2Mb608f3c5 renaming h209 → _p2mH209
end
open _root_.P2Mb608f3c5 renaming h32 → _p2mH32
open _root_.P2Mb608f3c5 renaming h33 → _p2mH33
open _root_.P2Mb608f3c5 renaming h34 → _p2mH34
open _root_.P2Mb608f3c5 renaming h35 → _p2mH35
namespace CurrentAFT.BackgroundEvaluation
end CurrentAFT.BackgroundEvaluation
namespace CurrentAFT.BackgroundEvaluation.bodyForm
end CurrentAFT.BackgroundEvaluation.bodyForm
namespace CurrentAFT.BackgroundFirstEvaluation
end CurrentAFT.BackgroundFirstEvaluation
namespace CurrentAFT.GlobalRaising
end CurrentAFT.GlobalRaising
namespace CurrentAFT.GlobalRaising.bodyPoint
end CurrentAFT.GlobalRaising.bodyPoint
namespace CurrentAFT.GlobalRaising.homogeneousCorrectionLinear
end CurrentAFT.GlobalRaising.homogeneousCorrectionLinear
namespace CurrentAFT.GlobalRaising.primaryPoint
end CurrentAFT.GlobalRaising.primaryPoint
namespace CurrentAFT.GlobalRaising.raisedPoint
end CurrentAFT.GlobalRaising.raisedPoint
namespace CurrentAFT.GlobalRaising.raisingLinear
end CurrentAFT.GlobalRaising.raisingLinear
namespace CurrentAFT.GlobalRaising.responseInverse
end CurrentAFT.GlobalRaising.responseInverse
namespace CurrentAFT.GlobalRaising.responseLinear
end CurrentAFT.GlobalRaising.responseLinear
namespace CurrentAFT.GlobalRaising.selectedCorrection
end CurrentAFT.GlobalRaising.selectedCorrection
namespace CurrentAFT.GlobalRaising.selectedCorrectionLinear
end CurrentAFT.GlobalRaising.selectedCorrectionLinear
namespace CurrentAFT.GlobalRaising.selectedPointProduct
end CurrentAFT.GlobalRaising.selectedPointProduct
namespace CurrentAFT.PrimaryMassFamilies
end CurrentAFT.PrimaryMassFamilies
namespace CurrentAFT.PrimaryMassFamilies.massCertificateFamily
end CurrentAFT.PrimaryMassFamilies.massCertificateFamily
namespace CurrentAFT.PrimaryMassFamilies.massLiftKernel
end CurrentAFT.PrimaryMassFamilies.massLiftKernel
namespace CurrentAFT.PrimaryMassFamilies.oneWordProfile
end CurrentAFT.PrimaryMassFamilies.oneWordProfile
namespace CurrentAFT.PrimaryMassFamilies.pairWordProfile
end CurrentAFT.PrimaryMassFamilies.pairWordProfile
namespace CurrentAFT.PrimaryMassFamilies.primaryArity
end CurrentAFT.PrimaryMassFamilies.primaryArity
section
namespace CurrentAFT.OrdinaryRaising
open AFT DiffuseProfiles ProposalPrimary ActualControls FringeCertificate BackgroundCertificates
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse GradedInverseNorm LocalCoefficientFamily LocalRaisingFirst LocalRaisingBounds
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies LocalReferenceEnergy
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.OrdinaryRaising.classicalFinDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h72 (security order : ℕ) (horder : 1 ≤ order)
    (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) (hcentered : (_root_.CurrentAFT.ActualControls.bodyReference security).expectation score = 0) :
    _root_.CurrentAFT.OrdinaryRaising.normalizedFamily security order horder score hcentered =
      _root_.CurrentAFT.BackgroundFamilies.bodyFamily (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder score hcentered +
        _root_.CurrentAFT.OrdinaryRaising.raisingFamily security order horder score hcentered := by
  unfold _root_.CurrentAFT.OrdinaryRaising.normalizedFamily _root_.CurrentAFT.OrdinaryRaising.raisingFamily
  rw [mul_sub, mul_one]
  abel
open _root_.P2Mb608f3c5 renaming h72 → _p2mH72
end
open _root_.P2Mb608f3c5 renaming h72 → _p2mH72
end CurrentAFT.OrdinaryRaising
open _root_.P2Mb608f3c5 renaming h72 → _p2mH72
end
open _root_.P2Mb608f3c5 renaming h72 → _p2mH72
namespace CurrentAFT.CycleSelections
end CurrentAFT.CycleSelections
namespace CurrentAFT.CycleSelections.averagedSelectedLaw
end CurrentAFT.CycleSelections.averagedSelectedLaw
namespace CurrentAFT.CycleSelections.currentRootTag
end CurrentAFT.CycleSelections.currentRootTag
namespace CurrentAFT.CycleSelections.selectionPermutation
end CurrentAFT.CycleSelections.selectionPermutation
namespace CurrentAFT.SupportedHoeffding
end CurrentAFT.SupportedHoeffding
section
namespace CurrentAFT.CycleRootExpansion
open AFT CycleSelections
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Index Color Value : Type*} [Fintype Index] [DecidableEq Index] [Fintype Color]
  [AddCommGroup Value] [Module ℝ Value]
section Actual
attribute [local instance] _root_.CurrentAFT.CycleRootExpansion.currentModulusNeZero
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h43 (security : ℕ) : 2 ≤ _root_.CurrentAFT.Parameters.bodySize security := by
  have hbase := _root_.CurrentAFT.Parameters.base_ge_two security
  have hmod := (_root_.CurrentAFT.Parameters.modulus_spec security).2.two_le
  have hpower : 1 ≤ _root_.CurrentAFT.Parameters.base security ^ 96 := one_le_pow₀ (by omega)
  rw [_root_.CurrentAFT.Parameters.bodySize_eq]
  exact hmod.trans (by simpa using Nat.mul_le_mul_left (_root_.CurrentAFT.Parameters.modulus security) hpower)
open _root_.P2Mb608f3c5 renaming h43 → _p2mH43
variable {Control : Type*} [Fintype Control]
end Actual
open _root_.P2Mb608f3c5 renaming h43 → _p2mH43
end
open _root_.P2Mb608f3c5 renaming h43 → _p2mH43
end CurrentAFT.CycleRootExpansion
open _root_.P2Mb608f3c5 renaming h43 → _p2mH43
end
open _root_.P2Mb608f3c5 renaming h43 → _p2mH43
namespace CurrentAFT.SelectedOrdinaryMean
end CurrentAFT.SelectedOrdinaryMean
section
namespace CurrentAFT.SelectedOrdinaryHybrid
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse LocalCoefficientFamily LocalRaisingLinear LocalRaisingFirst LocalRaisingBounds CoefficientHilbert
  SelectedOrdinaryRoot SelectedOrdinaryMean
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.SelectedOrdinaryHybrid.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.SelectedOrdinaryHybrid.safeDecidableEq
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h199 (security order : ℕ) (horder : 1 ≤ order) (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.SelectedOrdinaryHybrid.independentChannel security order horder score = _root_.CurrentAFT.RaisingChannels.bodyLeading security order horder score +
      _root_.CurrentAFT.RaisingChannels.bodyRaised security order horder score := by
  exact _p2mH72 security order horder _ _
open _root_.P2Mb608f3c5 renaming h199 → _p2mH199
end
open _root_.P2Mb608f3c5 renaming h199 → _p2mH199
end CurrentAFT.SelectedOrdinaryHybrid
open _root_.P2Mb608f3c5 renaming h199 → _p2mH199
end
open _root_.P2Mb608f3c5 renaming h199 → _p2mH199
namespace CurrentAFT.ActualRootGroupedChannel
end CurrentAFT.ActualRootGroupedChannel
namespace CurrentAFT.ActualRootGroupedChannel.channel
end CurrentAFT.ActualRootGroupedChannel.channel
namespace CurrentAFT.GroupedFamilyComposition
end CurrentAFT.GroupedFamilyComposition
section
namespace CurrentAFT.ActualRootResponse
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  GradedControlAlgebra ControlCoordinates LocalCoefficientFamily GradedInverse ControlNorm
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualRootResponse.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootResponse.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootResponse.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h29 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.ActualRootResponse.response order horder queue selection tagged layout kernel =
      _root_.CurrentAFT.GroupedFamilyTensor.response (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
        (_root_.CurrentAFT.ActualRootGroupedChannel.channel order horder queue selection tagged) (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel) := rfl
open _root_.P2Mb608f3c5 renaming h29 → _p2mH29
end
open _root_.P2Mb608f3c5 renaming h29 → _p2mH29
end CurrentAFT.ActualRootResponse
open _root_.P2Mb608f3c5 renaming h29 → _p2mH29
end
open _root_.P2Mb608f3c5 renaming h29 → _p2mH29
namespace CurrentAFT.FiniteAtomMoments
end CurrentAFT.FiniteAtomMoments
namespace CurrentAFT.TaggedOutputFock
end CurrentAFT.TaggedOutputFock
section
namespace CurrentAFT.UniformTaggedOutput
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock ActualBlockMean
  ActualCycleMeanMGF ConditionalHistogramMean PhysicalFockRates ActualFockBound TaggedSelection
  JointTaggedPhysicalFock TaggedOutputFock ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius BackgroundRates.ordinaryPool
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h200 (security r s : ℕ) (hprimary : r ≤ _root_.CurrentAFT.Parameters.legCount security)
    (hbody : s ≤ _root_.CurrentAFT.BackgroundRates.ordinaryPool security) (choice : _root_.CurrentAFT.UniformTaggedOutput.Choice security r s) :
    (_root_.CurrentAFT.UniformTaggedOutput.choiceLaw security r s hprimary hbody).weight choice =
      1 / (((_root_.CurrentAFT.Parameters.legCount security).descFactorial r : ℝ) *
        ((_root_.CurrentAFT.BackgroundRates.ordinaryPool security).descFactorial s : ℝ)) := by
  simp only [_root_.CurrentAFT.UniformTaggedOutput.choiceLaw, _root_.AFT.FiniteDist.prod_weight, _root_.AFT.FiniteDist.uniform_weight,
    Fintype.card_embedding_eq, Fintype.card_fin]
  ring
open _root_.P2Mb608f3c5 renaming h200 → _p2mH200
end
open _root_.P2Mb608f3c5 renaming h200 → _p2mH200
end CurrentAFT.UniformTaggedOutput
open _root_.P2Mb608f3c5 renaming h200 → _p2mH200
end
open _root_.P2Mb608f3c5 renaming h200 → _p2mH200
namespace CurrentAFT.ActualCalibrationIteration
end CurrentAFT.ActualCalibrationIteration
namespace CurrentAFT.ActualCalibrationIteration.iterate
end CurrentAFT.ActualCalibrationIteration.iterate
namespace CurrentAFT.ActualCalibrationIteration.iterate.match_1
end CurrentAFT.ActualCalibrationIteration.iterate.match_1
namespace CurrentAFT.ActualCalibrationIteration.step
end CurrentAFT.ActualCalibrationIteration.step
section
namespace CurrentAFT.ActualCoordinateBounds
open AFT ActualControls ProposalPrimary ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm BackgroundRates LocalCoefficientFamily
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualCoordinateBounds.coordinateFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h28 {State : Type*} [Fintype State] (reference : _root_.AFT.FiniteDist State)
    (test : State → ℝ) (bound : ℝ) (hbound : 1 ≤ bound)
    (point : State) (hatom : 1 ≤ bound * reference.weight point) :
    |test point| ≤ bound * Real.sqrt (reference.l2Sq test) := by
  have he : 0 ≤ reference.l2Sq test := _root_.AFT.FiniteDist.l2Sq_nonneg _ _
  have hp : reference.weight point * test point ^ 2 ≤ reference.l2Sq test :=
    Finset.single_le_sum (fun value _ => mul_nonneg (reference.nonneg value) (sq_nonneg _))
      (Finset.mem_univ point)
  have hs : test point ^ 2 ≤ bound * reference.l2Sq test := by
    have hfirst := mul_le_mul_of_nonneg_right hatom (sq_nonneg (test point))
    have hsecond := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ bound)
    nlinarith only [hfirst, hsecond]
  have hbb : bound ≤ bound ^ 2 := by nlinarith
  have hlarge := mul_le_mul_of_nonneg_right hbb he
  have hsqrt := Real.sq_sqrt he
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by linarith) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, hsqrt]
  exact hs.trans hlarge
open _root_.P2Mb608f3c5 renaming h28 → _p2mH28
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h22 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (bound : ℝ) (hbound : 1 ≤ bound)
    (hp : ∀ color, 1 ≤ bound * primary.weight color) (hb : ∀ color, 1 ≤ bound * body.weight color)
    {r s : ℕ} (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := Primary) (Body := Body) r s)
    (colors : Fin r → Primary) (centers : Fin s → Body) :
    |kernel colors centers| ≤ bound ^ (r + s) * _root_.CurrentAFT.ControlNorm.blockL2 primary body kernel := by
  let reference := (_root_.AFT.FiniteDist.independent (fun _ : Fin r => primary)).prod
    (_root_.AFT.FiniteDist.independent (fun _ : Fin s => body))
  have hatom : 1 ≤ bound ^ (r + s) * reference.weight (colors, centers) := by
    have hfirst : (1 : ℝ) ≤ ∏ index : Fin r, bound * primary.weight (colors index) :=
      Finset.one_le_prod (fun index _ => hp (colors index))
    have hsecond : (1 : ℝ) ≤ ∏ index : Fin s, bound * body.weight (centers index) :=
      Finset.one_le_prod (fun index _ => hb (centers index))
    have hprod := one_le_mul_of_one_le_of_one_le hfirst hsecond
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
    change 1 ≤ bound ^ (r + s) * ((∏ index, primary.weight (colors index)) *
      ∏ index, body.weight (centers index))
    rw [pow_add]
    nlinarith only [hprod]
  exact _p2mH28 reference (fun pair => kernel pair.1 pair.2) _
    (one_le_pow₀ hbound) (colors, centers) hatom
open _root_.P2Mb608f3c5 renaming h22 → _p2mH22
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h23 (security r s : ℕ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.ActualControls.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s)
    (colors : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |kernel colors centers| ≤ (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)) ^ (r + s) *
      _root_.CurrentAFT.ControlNorm.blockL2 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) kernel := by
  have hq := _root_.CurrentAFT.FirstResponse.modulus_pos security
  have hq1 : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.modulus security := by exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_spec security).2.one_le
  apply _p2mH22 _ _ _ (by linarith)
  · intro color
    have h := _root_.CurrentAFT.ProposalPrimary.primaryProfile_atom_lower security color
    have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * (Parameters.modulus security : ℝ))
    simpa only [_root_.CurrentAFT.ProposalPrimary.primaryLaw, mul_one_div_cancel (by positivity : (2 * (Parameters.modulus security : ℝ)) ≠ 0)] using hm
  · intro color
    have hm := mul_le_mul_of_nonneg_left (_root_.CurrentAFT.ActualControls.bodyReference_lower security color)
      (by positivity : 0 ≤ 2 * (Parameters.modulus security : ℝ))
    simpa only [mul_one_div_cancel (by positivity : (2 * (Parameters.modulus security : ℝ)) ≠ 0)] using hm
open _root_.P2Mb608f3c5 renaming h23 → _p2mH23
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h25 (security : ℕ) : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.dimension security := by
  have h := (_root_.CurrentAFT.Parameters.dimension_bounds security).1
  have hp := pow_pos (_root_.CurrentAFT.Parameters.base_pos security) 160
  exact_mod_cast (show 1 ≤ _root_.CurrentAFT.Parameters.dimension security by omega)
open _root_.P2Mb608f3c5 renaming h25 → _p2mH25
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h26 (security : ℕ) :
    1 ≤ (_root_.CurrentAFT.Parameters.dimension security : ℝ) * _root_.CurrentAFT.BackgroundRates.primaryFactor security := by
  have hd := _p2mH25 security
  have hl : (_root_.CurrentAFT.Parameters.legCount security : ℝ) ≤ _root_.CurrentAFT.Parameters.dimension security := by
    exact_mod_cast (show _root_.CurrentAFT.Parameters.legCount security ≤ _root_.CurrentAFT.Parameters.dimension security by
      unfold _root_.CurrentAFT.Parameters.dimension; omega)
  have hlpos : (0 : ℝ) < _root_.CurrentAFT.Parameters.legCount security := by
    have h : 0 < _root_.CurrentAFT.Parameters.legCount security := by
      unfold _root_.CurrentAFT.Parameters.legCount _root_.CurrentAFT.Parameters.scale
      exact pow_pos (pow_pos (_root_.CurrentAFT.Parameters.base_pos security) _) _
    exact_mod_cast h
  have hsqrt : Real.sqrt (_root_.CurrentAFT.Parameters.legCount security : ℝ) ≤ _root_.CurrentAFT.Parameters.dimension security := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith
    · nlinarith
  unfold _root_.CurrentAFT.BackgroundRates.primaryFactor
  rw [← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.mpr hlpos), one_mul]
  exact hsqrt
open _root_.P2Mb608f3c5 renaming h26 → _p2mH26
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h24 (security : ℕ) :
    1 ≤ (_root_.CurrentAFT.Parameters.dimension security : ℝ) * _root_.CurrentAFT.BackgroundRates.bodyFactor security := by
  have hd := _p2mH25 security
  have hp : (0 : ℝ) < _root_.CurrentAFT.BackgroundRates.ordinaryPool security := by exact_mod_cast _root_.CurrentAFT.BackgroundRates.ordinaryPool_pos security
  have hpool : (_root_.CurrentAFT.BackgroundRates.ordinaryPool security : ℝ) ≤ _root_.CurrentAFT.Parameters.dimension security := by
    exact_mod_cast (show _root_.CurrentAFT.BackgroundRates.ordinaryPool security ≤ _root_.CurrentAFT.Parameters.dimension security by
      unfold _root_.CurrentAFT.BackgroundRates.ordinaryPool _root_.CurrentAFT.Parameters.dimension; omega)
  have hr : (1 : ℝ) ≤ _root_.CurrentAFT.BackgroundRates.radius security := by
    apply Real.one_le_rpow
    · exact_mod_cast (_root_.CurrentAFT.Parameters.base_ge_two security).trans' (by omega)
    · norm_num
  have hsqrt : Real.sqrt (_root_.CurrentAFT.BackgroundRates.ordinaryPool security : ℝ) ≤ _root_.CurrentAFT.Parameters.dimension security := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith
    · nlinarith
  unfold _root_.CurrentAFT.BackgroundRates.bodyFactor
  rw [← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.mpr hp), one_mul]
  exact hsqrt.trans (le_mul_of_one_le_right (by linarith) hr)
open _root_.P2Mb608f3c5 renaming h24 → _p2mH24
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h27 (security order : ℕ) (family : _root_.CurrentAFT.LocalCoefficientFamily.Family security order)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(family arity).val colors centers| ≤
      (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) * _root_.CurrentAFT.Parameters.dimension security)^order *
        _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order family := by
  have hd := _p2mH25 security
  have hp := (_root_.CurrentAFT.RaisingPatternBudget.primaryFactor_pos security).le
  have hb := (_root_.CurrentAFT.RaisingPatternBudget.bodyFactor_pos security).le
  have hn := _root_.CurrentAFT.GradedControlNorm.familyNorm_nonneg (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order _ _ hp hb family
  have hweight : 1 ≤ (_root_.CurrentAFT.Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
      _root_.CurrentAFT.ControlNorm.gradeWeight (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security) arity.val.1.val arity.val.2.val := by
    have h := one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (_p2mH26 security) (n := arity.val.1.val))
      (one_le_pow₀ (_p2mH24 security) (n := arity.val.2.val))
    simpa only [_root_.CurrentAFT.ControlNorm.gradeWeight, mul_pow, pow_add, mul_mul_mul_comm] using h
  have hsingle : _root_.CurrentAFT.ControlNorm.gradeWeight (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security) arity.val.1.val arity.val.2.val *
      _root_.CurrentAFT.ControlNorm.blockL2 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (family arity).val ≤
        _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order family := by
    unfold _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm _root_.CurrentAFT.GradedControlNorm.familyNorm
    exact Finset.single_le_sum (fun index _ => mul_nonneg
      (_root_.CurrentAFT.ControlNorm.gradeWeight_nonneg _ _ hp hb index.val.1.val index.val.2.val)
      (_root_.CurrentAFT.ControlNorm.blockL2_nonneg (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (family index).val))
      (Finset.mem_univ arity)
  have hblock : _root_.CurrentAFT.ControlNorm.blockL2 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (family arity).val ≤
      (_root_.CurrentAFT.Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
        _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order family := by
    have hfirst := mul_le_mul_of_nonneg_right hweight (_root_.CurrentAFT.ControlNorm.blockL2_nonneg (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (family arity).val)
    have hsecond := mul_le_mul_of_nonneg_left hsingle
      (pow_nonneg (by linarith : (0 : ℝ) ≤ Parameters.dimension security) (arity.val.1.val + arity.val.2.val))
    nlinarith only [hfirst, hsecond]
  have hq : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.modulus security := by exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_spec security).2.one_le
  have hlarge : (1 : ℝ) ≤ 2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) * _root_.CurrentAFT.Parameters.dimension security := by nlinarith
  calc
    _ ≤ (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))^(arity.val.1.val + arity.val.2.val) *
        _root_.CurrentAFT.ControlNorm.blockL2 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (family arity).val := _p2mH23 security _ _ _ _ _
    _ ≤ (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))^(arity.val.1.val + arity.val.2.val) *
        ((_root_.CurrentAFT.Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
          _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order family) := mul_le_mul_of_nonneg_left hblock (by positivity)
    _ = (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) * _root_.CurrentAFT.Parameters.dimension security)^(arity.val.1.val + arity.val.2.val) *
        _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order family := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlarge arity.property) hn
open _root_.P2Mb608f3c5 renaming h27 → _p2mH27
end
open _root_.P2Mb608f3c5 renaming h22 → _p2mH22
open _root_.P2Mb608f3c5 renaming h23 → _p2mH23
open _root_.P2Mb608f3c5 renaming h24 → _p2mH24
open _root_.P2Mb608f3c5 renaming h25 → _p2mH25
open _root_.P2Mb608f3c5 renaming h26 → _p2mH26
open _root_.P2Mb608f3c5 renaming h27 → _p2mH27
open _root_.P2Mb608f3c5 renaming h28 → _p2mH28
end CurrentAFT.ActualCoordinateBounds
open _root_.P2Mb608f3c5 renaming h22 → _p2mH22
open _root_.P2Mb608f3c5 renaming h23 → _p2mH23
open _root_.P2Mb608f3c5 renaming h24 → _p2mH24
open _root_.P2Mb608f3c5 renaming h25 → _p2mH25
open _root_.P2Mb608f3c5 renaming h26 → _p2mH26
open _root_.P2Mb608f3c5 renaming h27 → _p2mH27
open _root_.P2Mb608f3c5 renaming h28 → _p2mH28
end
open _root_.P2Mb608f3c5 renaming h22 → _p2mH22
open _root_.P2Mb608f3c5 renaming h23 → _p2mH23
open _root_.P2Mb608f3c5 renaming h24 → _p2mH24
open _root_.P2Mb608f3c5 renaming h25 → _p2mH25
open _root_.P2Mb608f3c5 renaming h26 → _p2mH26
open _root_.P2Mb608f3c5 renaming h27 → _p2mH27
open _root_.P2Mb608f3c5 renaming h28 → _p2mH28
namespace CurrentAFT.CalibrationPointCoordinates
end CurrentAFT.CalibrationPointCoordinates
namespace CurrentAFT.CalibrationPointCoordinates.currentMatrix
end CurrentAFT.CalibrationPointCoordinates.currentMatrix
namespace CurrentAFT.CalibrationPointCoordinates.decode
end CurrentAFT.CalibrationPointCoordinates.decode
namespace CurrentAFT.CalibrationPointCoordinates.extend
end CurrentAFT.CalibrationPointCoordinates.extend
namespace CurrentAFT.CanonicalReconstruction
end CurrentAFT.CanonicalReconstruction
namespace CurrentAFT.CanonicalReconstruction.pointKernel
end CurrentAFT.CanonicalReconstruction.pointKernel
section
namespace CurrentAFT.CalibrationCoordinateError
open AFT ControlCoordinates ControlProduct ControlNorm CanonicalReconstruction
  GradedControlAlgebra GradedControlNorm CalibrationPointCoordinates
  ActualControls ProposalPrimary BackgroundRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.CalibrationCoordinateError.coordinateFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h30 {State : Type*} [Fintype State]
    (law : _root_.AFT.FiniteDist State) (value : State → ℝ) (bound : ℝ)
    (hbound : ∀ state, |value state| ≤ bound) : |law.expectation value| ≤ bound := by
  unfold _root_.AFT.FiniteDist.expectation
  calc
    _ ≤ ∑ state, |law.weight state * value state| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ state, law.weight state * bound := by
      apply Finset.sum_le_sum
      intro state _
      rw [abs_mul, abs_of_nonneg (law.nonneg state)]
      exact mul_le_mul_of_nonneg_left (hbound state) (law.nonneg state)
    _ = bound := by rw [← Finset.sum_mul, law.sum_one, one_mul]
open _root_.P2Mb608f3c5 renaming h30 → _p2mH30
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
end
open _root_.P2Mb608f3c5 renaming h30 → _p2mH30
end CurrentAFT.CalibrationCoordinateError
open _root_.P2Mb608f3c5 renaming h30 → _p2mH30
end
open _root_.P2Mb608f3c5 renaming h30 → _p2mH30
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
namespace AFT.BinaryArithmetic.RationalBits
end AFT.BinaryArithmetic.RationalBits
namespace AFT.BinaryArithmetic.RationalBits.iteration
end AFT.BinaryArithmetic.RationalBits.iteration
namespace AFT.BinaryArithmetic.RationalBits.iteration.match_1
end AFT.BinaryArithmetic.RationalBits.iteration.match_1
namespace AFT.BinaryArithmetic.RationalBits.iterationEntry
end AFT.BinaryArithmetic.RationalBits.iterationEntry
namespace AFT.BinaryArithmetic.RationalBits.iterationWorkStep
end AFT.BinaryArithmetic.RationalBits.iterationWorkStep
namespace AFT.BinaryArithmetic.RationalBits.matrixApply
end AFT.BinaryArithmetic.RationalBits.matrixApply
namespace AFT.BinaryArithmetic.RationalBits.matrixEntry
end AFT.BinaryArithmetic.RationalBits.matrixEntry
namespace AFT.BinaryArithmetic.RationalBits.matrixProductTerm
end AFT.BinaryArithmetic.RationalBits.matrixProductTerm
namespace AFT.BinaryArithmetic.RationalBits.matrixRow
end AFT.BinaryArithmetic.RationalBits.matrixRow
namespace CurrentAFT.CalibrationCoordinateError
end CurrentAFT.CalibrationCoordinateError
section
namespace CurrentAFT.CalibrationTableNorm
open AFT ActualControls ProposalPrimary LocalCoefficientFamily BackgroundRates
  CalibrationPointCoordinates CalibrationCoordinateError GradedControlAlgebra
  GradedControlNorm GradedControlStability ActualCompleteStability
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.CalibrationTableNorm.tableFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h31 (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    LinearMap.toMatrix' (_root_.CurrentAFT.CalibrationTableNorm.exactDefect security order horder hsecurity layout) =
      _root_.CurrentAFT.CalibrationPointCoordinates.currentMatrix security order horder hsecurity layout - 1 := by
  have he : _root_.CurrentAFT.CalibrationTableNorm.exactDefect security order horder hsecurity layout =
      _root_.CurrentAFT.CalibrationPointCoordinates.extend (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.ActualControls.primaryReference_positive security)
        (_root_.CurrentAFT.ActualControls.bodyReference_positive security) order
        (_root_.CurrentAFT.ActualCompleteStability.fullResponse security order horder (_root_.CurrentAFT.ActualCompleteStability.room security order horder hsecurity) layout) - LinearMap.id := by
    ext table point
    simp only [_root_.CurrentAFT.CalibrationTableNorm.exactDefect, _root_.CurrentAFT.CalibrationPointCoordinates.extend, _root_.CurrentAFT.CalibrationTableNorm.encodeCurrent, _root_.CurrentAFT.CalibrationTableNorm.decodeCurrent, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.comp_apply, map_sub, Pi.sub_apply]
    ring
  rw [he, map_sub]
  simp only [_root_.CurrentAFT.CalibrationPointCoordinates.currentMatrix, LinearMap.toMatrix'_id]
open _root_.P2Mb608f3c5 renaming h31 → _p2mH31
end
open _root_.P2Mb608f3c5 renaming h31 → _p2mH31
end CurrentAFT.CalibrationTableNorm
open _root_.P2Mb608f3c5 renaming h31 → _p2mH31
end
open _root_.P2Mb608f3c5 renaming h31 → _p2mH31
namespace CurrentAFT.BodyChannelEvaluation
end CurrentAFT.BodyChannelEvaluation
namespace CurrentAFT.BodyChannelEvaluation.bodyDensityChannel
end CurrentAFT.BodyChannelEvaluation.bodyDensityChannel
namespace CurrentAFT.BodyChannelEvaluation.bodyTensorMass
end CurrentAFT.BodyChannelEvaluation.bodyTensorMass
namespace CurrentAFT.BodyChannelEvaluation.safeMass
end CurrentAFT.BodyChannelEvaluation.safeMass
namespace CurrentAFT.CompleteRaising
end CurrentAFT.CompleteRaising
namespace CurrentAFT.CompleteRaising.homogeneousCorrectionLinear
end CurrentAFT.CompleteRaising.homogeneousCorrectionLinear
namespace CurrentAFT.CompleteRaising.selectedCorrection
end CurrentAFT.CompleteRaising.selectedCorrection
namespace CurrentAFT.CompleteRaising.selectedCorrectionLinear
end CurrentAFT.CompleteRaising.selectedCorrectionLinear
namespace CurrentAFT.CompleteRaising.selectedPointProduct
end CurrentAFT.CompleteRaising.selectedPointProduct
namespace CurrentAFT.CompleteRaising.slotLeading
end CurrentAFT.CompleteRaising.slotLeading
namespace CurrentAFT.CompleteRaising.slotRaised
end CurrentAFT.CompleteRaising.slotRaised
namespace CurrentAFT.PointPolynomial
end CurrentAFT.PointPolynomial
section
namespace CurrentAFT.CompleteRaisingEvaluation
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalRaisingFirst LocalRaisingLinear
  BackgroundFamilies GlobalRaising CompleteRaising LeadingEvaluation PointPolynomial
  LocalCoefficientEvaluation BackgroundEvaluation PrimaryMassFamilies
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.CompleteRaisingEvaluation.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.CompleteRaisingEvaluation.classicalSumDecidableEq
attribute [local irreducible] Parameters.base primaryLaw bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h38 (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (colors : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security)
    (slot : Fin r ⊕ Fin s) :
    _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedSlot security order horder colors centers slot =
      _root_.CurrentAFT.CompleteRaising.slotLeading security order horder colors centers slot + _root_.CurrentAFT.CompleteRaising.slotRaised security order horder colors centers slot := by
  cases slot with
  | inl index =>
    change _root_.CurrentAFT.NormalizedLocalPolynomial.independentNormalized security order _ =
      _root_.CurrentAFT.GlobalRaising.primaryPoint security order horder _ + _root_.CurrentAFT.GlobalRaising.raisedPoint security order horder _
    change _ = _root_.CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear security order horder _ +
      (_root_.CurrentAFT.NormalizedLocalPolynomial.independentNormalized security order _ - _root_.CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear security order horder _)
    abel
  | inr index =>
    exact _p2mH72 security order horder _ _
open _root_.P2Mb608f3c5 renaming h38 → _p2mH38
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h39 (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (colors : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    (∏ slot, _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedSlot security order horder colors centers slot) =
      ∑ selected, _root_.CurrentAFT.CompleteRaising.selectedPointProduct security order horder selected colors centers := by
  simp_rw [_p2mH38, add_comm (_root_.CurrentAFT.CompleteRaising.slotLeading security order horder colors centers _)]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro selected _
  simp [_root_.CurrentAFT.CompleteRaising.selectedPointProduct, Finset.prod_ite, ← Finset.mem_compl]
open _root_.P2Mb608f3c5 renaming h39 → _p2mH39
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h37 (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order horder kernel =
      ∑ selected, _root_.CurrentAFT.CompleteRaising.selectedCorrection security order horder selected kernel := by
  unfold _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint _root_.CurrentAFT.CompleteRaising.selectedCorrection
  simp_rw [_p2mH39, Finset.smul_sum]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext colors
    rw [Finset.sum_comm]
open _root_.P2Mb608f3c5 renaming h37 → _p2mH37
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h36 (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order horder kernel =
      _root_.CurrentAFT.CompleteRaising.selectedCorrection security order horder ∅ kernel +
        _root_.CurrentAFT.CompleteRaising.homogeneousCorrectionLinear security order horder r s kernel := by
  rw [_p2mH37]
  simp only [_root_.CurrentAFT.CompleteRaising.homogeneousCorrectionLinear, LinearMap.sum_apply]
  change _ = _root_.CurrentAFT.CompleteRaising.selectedCorrection security order horder ∅ kernel +
    ∑ selected ∈ (Finset.univ : Finset (Finset (Fin r ⊕ Fin s))).erase ∅,
      _root_.CurrentAFT.CompleteRaising.selectedCorrection security order horder selected kernel
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ ∅)).symm
open _root_.P2Mb608f3c5 renaming h36 → _p2mH36
end
open _root_.P2Mb608f3c5 renaming h36 → _p2mH36
open _root_.P2Mb608f3c5 renaming h37 → _p2mH37
open _root_.P2Mb608f3c5 renaming h38 → _p2mH38
open _root_.P2Mb608f3c5 renaming h39 → _p2mH39
end CurrentAFT.CompleteRaisingEvaluation
open _root_.P2Mb608f3c5 renaming h36 → _p2mH36
open _root_.P2Mb608f3c5 renaming h37 → _p2mH37
open _root_.P2Mb608f3c5 renaming h38 → _p2mH38
open _root_.P2Mb608f3c5 renaming h39 → _p2mH39
end
open _root_.P2Mb608f3c5 renaming h36 → _p2mH36
open _root_.P2Mb608f3c5 renaming h37 → _p2mH37
open _root_.P2Mb608f3c5 renaming h38 → _p2mH38
open _root_.P2Mb608f3c5 renaming h39 → _p2mH39
namespace AFT.RationalNumerics.windowGaussianWeights
end AFT.RationalNumerics.windowGaussianWeights
namespace AFT.RationalNumerics.windowTicketCounts
end AFT.RationalNumerics.windowTicketCounts
namespace AFT.RationalNumerics.windowTicketLaw
end AFT.RationalNumerics.windowTicketLaw
namespace CurrentAFT.DiffuseProfiles
end CurrentAFT.DiffuseProfiles
namespace CurrentAFT.DiffuseProfiles.actual_clearance
end CurrentAFT.DiffuseProfiles.actual_clearance
namespace CurrentAFT.DiffuseProfiles.deletion
end CurrentAFT.DiffuseProfiles.deletion
namespace CurrentAFT.DiffuseProfiles.intervalStart
end CurrentAFT.DiffuseProfiles.intervalStart
namespace CurrentAFT.DiffuseProfiles.signProfile
end CurrentAFT.DiffuseProfiles.signProfile
namespace CurrentAFT.Parameters
end CurrentAFT.Parameters
namespace CurrentAFT.Parameters.anchorWidth
end CurrentAFT.Parameters.anchorWidth
namespace CurrentAFT.Parameters.sourceWidth
end CurrentAFT.Parameters.sourceWidth
section
namespace CurrentAFT.WindowGaussianSampler
open AFT GaussianSource RationalNumerics DiffuseProfiles
open scoped BigOperators Classical
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h207 (security : ℕ) : 0 < _root_.CurrentAFT.WindowGaussianSampler.squaredWidth security := by
  unfold _root_.CurrentAFT.WindowGaussianSampler.squaredWidth
  positivity
open _root_.P2Mb608f3c5 renaming h207 → _p2mH207
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h208 (security : ℕ) :
    (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security : ℝ) = (_root_.CurrentAFT.Parameters.sourceWidth security : ℝ)^2 := by
  unfold _root_.CurrentAFT.WindowGaussianSampler.squaredWidth _root_.CurrentAFT.Parameters.sourceWidth _root_.CurrentAFT.Parameters.base
  push_cast
  rfl
open _root_.P2Mb608f3c5 renaming h208 → _p2mH208
noncomputable section
end
end CurrentAFT.WindowGaussianSampler
open _root_.P2Mb608f3c5 renaming h207 → _p2mH207
open _root_.P2Mb608f3c5 renaming h208 → _p2mH208
end
open _root_.P2Mb608f3c5 renaming h207 → _p2mH207
open _root_.P2Mb608f3c5 renaming h208 → _p2mH208
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace CurrentAFT.CycleSelections.Adjacent
end CurrentAFT.CycleSelections.Adjacent
namespace CurrentAFT.CycleSelections.latentSupport
end CurrentAFT.CycleSelections.latentSupport
namespace CurrentAFT.CycleSelections.pairLaw
end CurrentAFT.CycleSelections.pairLaw
namespace CurrentAFT.CycleSelections.selectedLaw
end CurrentAFT.CycleSelections.selectedLaw
namespace CurrentAFT.CycleSelections.selectionLaw
end CurrentAFT.CycleSelections.selectionLaw
namespace CurrentAFT.CycleSelections.singletonDensity
end CurrentAFT.CycleSelections.singletonDensity
namespace CurrentAFT.JointTaggedPhysicalFock
end CurrentAFT.JointTaggedPhysicalFock
namespace CurrentAFT.JointTaggedPhysicalFock.reduceBody
end CurrentAFT.JointTaggedPhysicalFock.reduceBody
namespace CurrentAFT.JointTaggedPhysicalFock.reducePrimary
end CurrentAFT.JointTaggedPhysicalFock.reducePrimary
namespace CurrentAFT.Parameters.sourceCutoff
end CurrentAFT.Parameters.sourceCutoff
namespace CurrentAFT.ProtectedCycle
end CurrentAFT.ProtectedCycle
namespace CurrentAFT.ProtectedCycle.gaussianCycleLaw
end CurrentAFT.ProtectedCycle.gaussianCycleLaw
namespace CurrentAFT.ProtectedCycle.scalarFourier
end CurrentAFT.ProtectedCycle.scalarFourier
namespace CurrentAFT.TensorPublicProjection
end CurrentAFT.TensorPublicProjection
namespace CurrentAFT.WindowGaussianSampler
end CurrentAFT.WindowGaussianSampler
section
namespace CurrentAFT.CyclePatternProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h42 {State : Type*} [Fintype State] (first second : _root_.AFT.FiniteDist State)
    (test : State → ℝ) (bound : ℝ) (htest : ∀ state, |test state| ≤ bound) :
    |first.expectation test - second.expectation test| ≤
      bound * ∑ state, |first.weight state - second.weight state| := by
  unfold _root_.AFT.FiniteDist.expectation
  rw [← Finset.sum_sub_distrib]
  calc
    _ = |∑ state, (first.weight state - second.weight state) * test state| := by
      congr 1
      apply Finset.sum_congr rfl
      intro state _
      ring
    _ ≤ ∑ state, |(first.weight state - second.weight state) * test state| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ state, bound * |first.weight state - second.weight state| := by
      apply Finset.sum_le_sum
      intro state _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (htest state) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm
open _root_.P2Mb608f3c5 renaming h42 → _p2mH42
end
open _root_.P2Mb608f3c5 renaming h42 → _p2mH42
end CurrentAFT.CyclePatternProgram
open _root_.P2Mb608f3c5 renaming h42 → _p2mH42
end
open _root_.P2Mb608f3c5 renaming h42 → _p2mH42
namespace CurrentAFT.DiffuseProfiles.edgeCutoff
end CurrentAFT.DiffuseProfiles.edgeCutoff
namespace CurrentAFT.LocalDiffuseProgram
end CurrentAFT.LocalDiffuseProgram
namespace CurrentAFT.LocalDiffuseProgram.blurEntry
end CurrentAFT.LocalDiffuseProgram.blurEntry
namespace CurrentAFT.LocalMarkedProgram
end CurrentAFT.LocalMarkedProgram
namespace CurrentAFT.LocalMarkedProgram.blurEntry
end CurrentAFT.LocalMarkedProgram.blurEntry
namespace CurrentAFT.LocalMarkedProgram.coinEntry
end CurrentAFT.LocalMarkedProgram.coinEntry
namespace CurrentAFT.LocalMarkedProgram.pointEntry
end CurrentAFT.LocalMarkedProgram.pointEntry
section
namespace CurrentAFT.LocalPairProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles LocalReferenceEnergy
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h65 (security bits : ℕ) :
    |(_root_.CurrentAFT.LocalPairProgram.activationApprox security bits : ℝ) - _root_.CurrentAFT.DiffuseProfiles.activation security| ≤ (1/2:ℝ) * (1 / (2:ℝ)^bits) := by
  let law := _root_.AFT.RationalNumerics.windowApproxLaw (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security) (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) bits
  have hsum : (∑ point, |law.weight point - (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight point|) ≤ 1 / (2:ℝ)^bits :=
    _p2mH13 _ _ _ _ (_p2mH207 security)
      (_p2mH208 security).symm
  have hatom := Finset.single_le_sum (f := fun point => |law.weight point - (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight point|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ (_root_.AFT.GaussianSource.windowZero (_root_.CurrentAFT.Parameters.sourceCutoff security - 1)))
  have heq : (_root_.CurrentAFT.LocalPairProgram.activationApprox security bits : ℝ) = (1/2:ℝ)*law.weight (_root_.AFT.GaussianSource.windowZero _) := by
    simp only [_root_.CurrentAFT.LocalPairProgram.activationApprox, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    rfl
  rw [heq]
  unfold _root_.CurrentAFT.DiffuseProfiles.activation
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  exact mul_le_mul_of_nonneg_left (hatom.trans hsum) (by norm_num)
open _root_.P2Mb608f3c5 renaming h65 → _p2mH65
end
open _root_.P2Mb608f3c5 renaming h65 → _p2mH65
end CurrentAFT.LocalPairProgram
open _root_.P2Mb608f3c5 renaming h65 → _p2mH65
end
open _root_.P2Mb608f3c5 renaming h65 → _p2mH65
namespace CurrentAFT.CurrentGaussianBits
end CurrentAFT.CurrentGaussianBits
namespace CurrentAFT.CurrentGaussianBits.budget
end CurrentAFT.CurrentGaussianBits.budget
namespace CurrentAFT.CurrentGaussianBits.table
end CurrentAFT.CurrentGaussianBits.table
namespace CurrentAFT.CurrentGaussianBits.tableWork
end CurrentAFT.CurrentGaussianBits.tableWork
namespace CurrentAFT.CurrentGaussianBits.widthCode
end CurrentAFT.CurrentGaussianBits.widthCode
namespace CurrentAFT.CurrentGaussianBits.widthWork
end CurrentAFT.CurrentGaussianBits.widthWork
namespace CurrentAFT.CurrentGaussianBits.workPolynomial
end CurrentAFT.CurrentGaussianBits.workPolynomial
namespace CurrentAFT.LocalPairProgram
end CurrentAFT.LocalPairProgram
namespace CurrentAFT.LocalPairProgram.activationApprox
end CurrentAFT.LocalPairProgram.activationApprox
namespace CurrentAFT.ProposalPrimary
end CurrentAFT.ProposalPrimary
namespace CurrentAFT.ProposalPrimary.anchorPrimaryLaw
end CurrentAFT.ProposalPrimary.anchorPrimaryLaw
namespace CurrentAFT.ProposalPrimary.centerProfile
end CurrentAFT.ProposalPrimary.centerProfile
namespace CurrentAFT.ProposalPrimary.finite_safe_law_weight
end CurrentAFT.ProposalPrimary.finite_safe_law_weight
namespace CurrentAFT.RefinedPublicOutput
end CurrentAFT.RefinedPublicOutput
namespace CurrentAFT.RefinedPublicOutput.blockCharge
end CurrentAFT.RefinedPublicOutput.blockCharge
namespace CurrentAFT.RefinedPublicOutput.blocks
end CurrentAFT.RefinedPublicOutput.blocks
namespace CurrentAFT.RefinedPublicOutput.blocks.match_1
end CurrentAFT.RefinedPublicOutput.blocks.match_1
namespace CurrentAFT.WindowGaussianSampler.squaredWidth
end CurrentAFT.WindowGaussianSampler.squaredWidth
section
namespace CurrentAFT.RationalProposalProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h172 (security bits : ℕ) (primary output : _root_.CurrentAFT.FirstHistogram.Palette security) :
    |(_root_.CurrentAFT.RationalProposalProgram.anchor security bits primary.val output.val : ℝ) -
      (_root_.CurrentAFT.InwardAnchor.smoothedAnchorLaw security primary).weight output| ≤ 1 / (2 : ℝ)^bits := by
  rw [_root_.CurrentAFT.RationalProposalProgram.anchor_cast]
  have hl1 := _p2mH13 (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security)
    (_root_.CurrentAFT.Parameters.sourceWidth security) (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) bits
    (_p2mH207 security) (_p2mH208 security).symm
  have h := _p2mH42
    (_root_.AFT.RationalNumerics.windowApproxLaw (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security) (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) bits)
    (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security)
    (fun scalar => (_root_.CurrentAFT.InwardAnchor.shiftedAnchorLaw security primary scalar.val
      (_root_.CurrentAFT.InwardAnchor.scalar_bound security scalar)).weight output) 1 (fun scalar => by
      rw [abs_of_nonneg ((_root_.CurrentAFT.InwardAnchor.shiftedAnchorLaw security primary scalar.val
        (_root_.CurrentAFT.InwardAnchor.scalar_bound security scalar)).nonneg output)]
      exact (_root_.CurrentAFT.InwardAnchor.shiftedAnchorLaw security primary scalar.val
        (_root_.CurrentAFT.InwardAnchor.scalar_bound security scalar)).atom_le_one output)
  exact h.trans (by simpa only [one_mul,_root_.CurrentAFT.DiffuseProfiles.scalarLaw] using hl1)
open _root_.P2Mb608f3c5 renaming h172 → _p2mH172
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h184 (security bits : ℕ) :
    (∑ seed, |(_root_.CurrentAFT.RationalProposalProgram.approximateSeedLaw security bits).weight seed - (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).weight seed|) ≤
      3 / (2 : ℝ)^bits := by
  have he := _p2mH13 (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security) (_root_.CurrentAFT.Parameters.sourceWidth security)
    (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security) bits (_p2mH207 security)
    (_p2mH208 security).symm
  have hs := _p2mH13 (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security) (_root_.CurrentAFT.Parameters.sourceWidth security)
    (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) bits (_p2mH207 security)
    (_p2mH208 security).symm
  have hp := FiniteDist.l1_prod_le
    (_root_.AFT.RationalNumerics.windowApproxLaw (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security) (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security) bits)
    (_root_.CurrentAFT.DiffuseProfiles.edgeLaw security)
    (_root_.AFT.RationalNumerics.windowApproxLaw (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security) (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security) bits) (_root_.CurrentAFT.DiffuseProfiles.edgeLaw security)
  have hall := FiniteDist.l1_prod_le
    ((_root_.AFT.RationalNumerics.windowApproxLaw (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security) (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security) bits).prod
      (_root_.AFT.RationalNumerics.windowApproxLaw (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security) (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security) bits))
    ((_root_.CurrentAFT.DiffuseProfiles.edgeLaw security).prod (_root_.CurrentAFT.DiffuseProfiles.edgeLaw security))
    (_root_.AFT.RationalNumerics.windowApproxLaw (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security) (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) bits)
    (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security)
  exact hall.trans ((add_le_add (hp.trans (add_le_add he he)) hs).trans_eq (by ring))
open _root_.P2Mb608f3c5 renaming h184 → _p2mH184
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h174 (security bits : ℕ) (includeScalar : Bool) (output : _root_.CurrentAFT.FirstHistogram.Palette security) :
    |(_root_.CurrentAFT.RationalProposalProgram.body security bits includeScalar output.val : ℝ) - (_root_.CurrentAFT.ProposalPrimary.bodyLaw security includeScalar).weight output| ≤
      3 / (2 : ℝ)^bits := by
  rw [_root_.CurrentAFT.RationalProposalProgram.body_cast]
  exact (_p2mH42 (_root_.CurrentAFT.RationalProposalProgram.approximateSeedLaw security bits)
    (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security) (fun seed => ((_root_.CurrentAFT.ProposalPrimary.safeLaw security).map
      (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (_root_.CurrentAFT.DiffuseProfiles.actualBlur security seed + if includeScalar then _root_.CurrentAFT.DiffuseProfiles.actualSecond security seed else 0))).weight output)
      1 (fun seed => by
        rw [abs_of_nonneg (_root_.AFT.FiniteDist.nonneg _ _)]
        exact _root_.AFT.FiniteDist.atom_le_one _ _)).trans (by simpa only [one_mul] using _p2mH184 security bits)
open _root_.P2Mb608f3c5 renaming h174 → _p2mH174
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h178 (colors width output : ℕ) (blur second : ℤ) :
    |(_root_.CurrentAFT.RationalProposalProgram.diffuseKernel colors width blur second output : ℝ)| ≤ 1 := by
  have hp := _p2mH20 colors 1
    ((width : ℤ) + blur) second width output
  have hm := _p2mH20 colors 1
    (-2 * (width : ℤ) + 1 + blur) second width output
  simp only [_root_.CurrentAFT.RationalProposalProgram.diffuseKernel, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (by linarith only [hp, hm])
open _root_.P2Mb608f3c5 renaming h178 → _p2mH178
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h179 (security bits : ℕ) (output : _root_.CurrentAFT.FirstHistogram.Palette security) :
    |(_root_.CurrentAFT.RationalProposalProgram.diffuse security bits output.val : ℝ) - _root_.CurrentAFT.ProposalPrimary.diffuseMean security output| ≤ 3 / (2 : ℝ)^bits := by
  rw [_root_.CurrentAFT.RationalProposalProgram.diffuse_cast]
  change |_root_.CurrentAFT.RationalProposalProgram.fairProfile security (_root_.CurrentAFT.RationalProposalProgram.approximateSeedLaw security bits) output -
    _root_.CurrentAFT.RationalProposalProgram.fairProfile security (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security) output| ≤ _
  rw [_root_.CurrentAFT.RationalProposalProgram.fairProfile_expectation, _root_.CurrentAFT.RationalProposalProgram.fairProfile_expectation]
  exact (_p2mH42 _ _ _ 1
    (fun seed => _p2mH178 _ _ _ _ _)).trans
      (by simpa only [one_mul] using _p2mH184 security bits)
open _root_.P2Mb608f3c5 renaming h179 → _p2mH179
set_option maxRecDepth 8192
private theorem _root_.P2Mb608f3c5.h210
    (free legs colors dimension rate activation bzero bone diffuse primary
      bzero' bone' diffuse' epsilon : ℝ)
    (hfree : 0 ≤ free) (hlegs : 0 ≤ legs) (hcolors : 0 ≤ colors)
    (hdimension : free + 3 * legs + colors = dimension)
    (hrate : 0 ≤ rate ∧ rate ≤ 1) (hepsilon : 0 ≤ epsilon)
    (hbzero : 0 ≤ bzero ∧ bzero ≤ 1) (hdiffuse : 0 ≤ diffuse ∧ diffuse ≤ 1)
    (hprimary : 0 ≤ primary ∧ primary ≤ 1)
    (hzeroError : |bzero - bzero'| ≤ 3 * epsilon)
    (honeError : |bone - bone'| ≤ 3 * epsilon)
    (hdiffuseError : |diffuse - diffuse'| ≤ 3 * epsilon)
    (hrateError : |rate - activation| ≤ epsilon / 2)
    (hbalance : dimension / colors - (free + legs * activation) * bzero -
      (legs + colors) * bone - 2 * legs * (1 - activation) * diffuse = legs * activation * primary) :
    |dimension / colors - (free + legs * rate) * bzero' - (legs + colors) * bone' -
      2 * legs * (1 - rate) * diffuse' - legs * rate * primary| ≤ 8 * dimension * epsilon := by
  have hrateNonneg := hrate.1
  have hgap : |-bzero + 2 * diffuse - primary| ≤ 4 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hzero : |(free + legs * rate) * (bzero - bzero')| ≤ (free + legs) * (3 * epsilon) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ free + legs * rate)]
    exact mul_le_mul (by nlinarith) hzeroError (abs_nonneg _) (by positivity)
  have hone : |(legs + colors) * (bone - bone')| ≤ (legs + colors) * (3 * epsilon) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ legs + colors)]
    exact mul_le_mul_of_nonneg_left honeError (by positivity)
  have hdiff : |(2 * legs * (1 - rate)) * (diffuse - diffuse')| ≤ (2 * legs) * (3 * epsilon) := by
    have hcoef : 0 ≤ 2 * legs * (1 - rate) := mul_nonneg (by positivity) (by linarith only [hrate.2])
    rw [abs_mul, abs_of_nonneg hcoef]
    exact mul_le_mul (by nlinarith [hrate.1]) hdiffuseError (abs_nonneg _) (by positivity)
  have hrateTerm : |legs * (rate - activation) * (-bzero + 2 * diffuse - primary)| ≤
      (legs * (epsilon / 2)) * 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hlegs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hrateError hlegs) hgap (abs_nonneg _) (by positivity)
  have hdecompose : dimension / colors - (free + legs * rate) * bzero' - (legs + colors) * bone' -
      2 * legs * (1 - rate) * diffuse' - legs * rate * primary =
      (free + legs * rate) * (bzero - bzero') + (legs + colors) * (bone - bone') +
        (2 * legs * (1 - rate)) * (diffuse - diffuse') +
          legs * (rate - activation) * (-bzero + 2 * diffuse - primary) := by
    linear_combination hbalance
  rw [hdecompose]
  calc
    _ ≤ |(free + legs * rate) * (bzero - bzero')| + |(legs + colors) * (bone - bone')| +
        |(2 * legs * (1 - rate)) * (diffuse - diffuse')| +
          |legs * (rate - activation) * (-bzero + 2 * diffuse - primary)| :=
      (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (free + legs) * (3 * epsilon) + (legs + colors) * (3 * epsilon) +
        (2 * legs) * (3 * epsilon) + (legs * (epsilon / 2)) * 4 :=
      add_le_add (add_le_add (add_le_add hzero hone) hdiff) hrateTerm
    _ = (3 * free + 14 * legs + 3 * colors) * epsilon := by ring
    _ ≤ (8 * dimension) * epsilon :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hdimension, hfree, hlegs, hcolors]) hepsilon
    _ = _ := by ring
open _root_.P2Mb608f3c5 renaming h210 → _p2mH210
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h181 (security bits : ℕ) (output : _root_.CurrentAFT.FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (_root_.CurrentAFT.Parameters.base security : ℝ))) :
    |(_root_.CurrentAFT.RationalProposalProgram.primaryRaw security bits output.val : ℝ) - _root_.CurrentAFT.ProposalPrimary.primaryProfile security output| ≤
      64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let rate : ℝ := _root_.CurrentAFT.LocalPairProgram.activationApprox security bits
  have hepsilon : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have hb := _root_.CurrentAFT.FirstResponse.base_pos security
  have hrate := _root_.CurrentAFT.LocalPairProgram.activationApprox_bounds security bits
  have hrateError : |rate - _root_.CurrentAFT.DiffuseProfiles.activation security| ≤ epsilon / 2 := by
    exact (_p2mH65 security bits).trans_eq (by dsimp only [epsilon]; ring)
  have hrateLower : 1 / (8 * (_root_.CurrentAFT.Parameters.base security : ℝ)) ≤ rate := by
    have ha := _root_.CurrentAFT.FirstResponse.activation_lower_simple security
    have hfrac : 1 / (8 * (_root_.CurrentAFT.Parameters.base security : ℝ)) = (1 / (4 * (_root_.CurrentAFT.Parameters.base security : ℝ))) / 2 := by ring
    rw [hfrac]
    linarith [(abs_le.mp hrateError).1, hprecision]
  have hlegsPos : (0 : ℝ) < _root_.CurrentAFT.Parameters.legCount security := by
    exact_mod_cast (show 0 < _root_.CurrentAFT.Parameters.legCount security by
      rw [_root_.CurrentAFT.Parameters.legCount_eq]; exact pow_pos (_root_.CurrentAFT.Parameters.base_pos security) _)
  have hlegsOne : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.legCount security := by
    exact_mod_cast (show 1 ≤ _root_.CurrentAFT.Parameters.legCount security by
      have h : 0 < _root_.CurrentAFT.Parameters.legCount security := Nat.cast_pos.mp hlegsPos; omega)
  have hden : 0 < (_root_.CurrentAFT.Parameters.legCount security : ℝ) * rate :=
    mul_pos hlegsPos (_root_.CurrentAFT.RationalProposalProgram.activationApprox_pos security bits)
  have hdenLower : 1 / (8 * (_root_.CurrentAFT.Parameters.base security : ℝ)) ≤
      (_root_.CurrentAFT.Parameters.legCount security : ℝ) * rate :=
    hrateLower.trans (by nlinarith [_root_.CurrentAFT.RationalProposalProgram.activationApprox_pos security bits])
  have hdimension : _root_.CurrentAFT.ProposalPrimary.freeMass security + 3 * (_root_.CurrentAFT.Parameters.legCount security : ℝ) +
      _root_.CurrentAFT.Parameters.modulus security = _root_.CurrentAFT.Parameters.dimension security := by
    unfold _root_.CurrentAFT.ProposalPrimary.freeMass _root_.CurrentAFT.Parameters.dimension
    push_cast
    ring
  have hbalance : (_root_.CurrentAFT.Parameters.dimension security : ℝ) / _root_.CurrentAFT.Parameters.modulus security -
      (_root_.CurrentAFT.ProposalPrimary.freeMass security + (_root_.CurrentAFT.Parameters.legCount security : ℝ) * _root_.CurrentAFT.DiffuseProfiles.activation security) * (_root_.CurrentAFT.ProposalPrimary.bodyLaw security false).weight output -
      ((_root_.CurrentAFT.Parameters.legCount security : ℝ) + _root_.CurrentAFT.Parameters.modulus security) * (_root_.CurrentAFT.ProposalPrimary.bodyLaw security true).weight output -
      2 * _root_.CurrentAFT.Parameters.legCount security * (1 - _root_.CurrentAFT.DiffuseProfiles.activation security) * _root_.CurrentAFT.ProposalPrimary.diffuseMean security output =
      (_root_.CurrentAFT.Parameters.legCount security : ℝ) * _root_.CurrentAFT.DiffuseProfiles.activation security * _root_.CurrentAFT.ProposalPrimary.primaryProfile security output := by
    unfold _root_.CurrentAFT.ProposalPrimary.primaryProfile _root_.CurrentAFT.ProposalPrimary.markMass
    field_simp [(_root_.CurrentAFT.DiffuseProfiles.activation_pos security).ne', hlegsPos.ne']
  have hprimary : 0 ≤ _root_.CurrentAFT.ProposalPrimary.primaryProfile security output ∧ _root_.CurrentAFT.ProposalPrimary.primaryProfile security output ≤ 1 :=
    ⟨(_root_.CurrentAFT.ProposalPrimary.primaryLaw security).nonneg output, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).atom_le_one output⟩
  have hdiffuse : 0 ≤ _root_.CurrentAFT.ProposalPrimary.diffuseMean security output ∧ _root_.CurrentAFT.ProposalPrimary.diffuseMean security output ≤ 1 := by
    refine ⟨_root_.CurrentAFT.ProposalPrimary.diffuseMean_nonneg security output, ?_⟩
    rw [← _root_.CurrentAFT.ProposalPrimary.diffuseMean_mass security]
    exact Finset.single_le_sum (fun color _ => _root_.CurrentAFT.ProposalPrimary.diffuseMean_nonneg security color) (Finset.mem_univ output)
  have hzeroError : |(_root_.CurrentAFT.ProposalPrimary.bodyLaw security false).weight output - (_root_.CurrentAFT.RationalProposalProgram.approximateBodyLaw security bits false).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← _root_.CurrentAFT.RationalProposalProgram.body_cast]
    exact (_p2mH174 security bits false output).trans_eq (by dsimp only [epsilon]; ring)
  have honeError : |(_root_.CurrentAFT.ProposalPrimary.bodyLaw security true).weight output - (_root_.CurrentAFT.RationalProposalProgram.approximateBodyLaw security bits true).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← _root_.CurrentAFT.RationalProposalProgram.body_cast]
    exact (_p2mH174 security bits true output).trans_eq (by dsimp only [epsilon]; ring)
  have hdiffuseError : |_root_.CurrentAFT.ProposalPrimary.diffuseMean security output - (_root_.CurrentAFT.RationalProposalProgram.approximateDiffuseLaw security bits).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← _root_.CurrentAFT.RationalProposalProgram.diffuse_cast]
    exact (_p2mH179 security bits output).trans_eq (by dsimp only [epsilon]; ring)
  have hresidual := _p2mH210 (_root_.CurrentAFT.ProposalPrimary.freeMass security) (_root_.CurrentAFT.Parameters.legCount security)
    (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security) rate (_root_.CurrentAFT.DiffuseProfiles.activation security)
    ((_root_.CurrentAFT.ProposalPrimary.bodyLaw security false).weight output) ((_root_.CurrentAFT.ProposalPrimary.bodyLaw security true).weight output)
    (_root_.CurrentAFT.ProposalPrimary.diffuseMean security output) (_root_.CurrentAFT.ProposalPrimary.primaryProfile security output)
    ((_root_.CurrentAFT.RationalProposalProgram.approximateBodyLaw security bits false).weight output) ((_root_.CurrentAFT.RationalProposalProgram.approximateBodyLaw security bits true).weight output)
    ((_root_.CurrentAFT.RationalProposalProgram.approximateDiffuseLaw security bits).weight output) epsilon (_root_.CurrentAFT.ProposalPrimary.freeMass_nonneg security) hlegsPos.le
    (Nat.cast_nonneg _) hdimension ⟨hrate.1, by linarith only [hrate.2]⟩ hepsilon
    ⟨(_root_.CurrentAFT.ProposalPrimary.bodyLaw security false).nonneg output, (_root_.CurrentAFT.ProposalPrimary.bodyLaw security false).atom_le_one output⟩ hdiffuse hprimary
    hzeroError honeError hdiffuseError hrateError hbalance
  rw [_root_.CurrentAFT.RationalProposalProgram.primaryRaw_cast]
  have hquotient (numerator : ℝ) : |numerator / ((_root_.CurrentAFT.Parameters.legCount security : ℝ) * rate) -
      _root_.CurrentAFT.ProposalPrimary.primaryProfile security output| =
      |numerator - (_root_.CurrentAFT.Parameters.legCount security : ℝ) * rate * _root_.CurrentAFT.ProposalPrimary.primaryProfile security output| /
        ((_root_.CurrentAFT.Parameters.legCount security : ℝ) * rate) := by
    rw [div_sub' hden.ne', abs_div, abs_of_pos hden]
  rw [hquotient]
  calc
    _ ≤ (8 * _root_.CurrentAFT.Parameters.dimension security * epsilon) / ((_root_.CurrentAFT.Parameters.legCount security : ℝ) * rate) :=
      div_le_div_of_nonneg_right hresidual hden.le
    _ ≤ (8 * _root_.CurrentAFT.Parameters.dimension security * epsilon) / (1 / (8 * (_root_.CurrentAFT.Parameters.base security : ℝ))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdenLower
    _ = _ := by dsimp only [epsilon]; field_simp; ring
open _root_.P2Mb608f3c5 renaming h181 → _p2mH181
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h182 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (_root_.CurrentAFT.Parameters.base security : ℝ)))
    (hbudget : 64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) (output : _root_.CurrentAFT.FirstHistogram.Palette security) :
    1 / (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)) ≤ (_root_.CurrentAFT.RationalProposalProgram.primaryRaw security bits output.val : ℝ) := by
  have herr := (abs_le.mp (_p2mH181 security bits output hprecision)).1
  have hp := _root_.CurrentAFT.ProposalPrimary.primaryProfile_atom_lower security output
  have hfrac : (1 : ℝ) / (2 * _root_.CurrentAFT.Parameters.modulus security) = 2 * (1 / (4 * _root_.CurrentAFT.Parameters.modulus security)) := by ring
  rw [hfrac] at hp
  linarith
open _root_.P2Mb608f3c5 renaming h182 → _p2mH182
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h180 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (_root_.CurrentAFT.Parameters.base security : ℝ)))
    (hbudget : 64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) : _root_.CurrentAFT.RationalProposalProgram.primaryGood security bits := by
  unfold _root_.CurrentAFT.RationalProposalProgram.primaryGood
  rw [_root_.CurrentAFT.PublicParameterProgram.modulus_value]
  intro output
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
    _p2mH182 security bits hprecision hbudget output
open _root_.P2Mb608f3c5 renaming h180 → _p2mH180
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h183 (security bits : ℕ) (output : _root_.CurrentAFT.FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (_root_.CurrentAFT.Parameters.base security : ℝ)))
    (hbudget : 64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) :
    |(_root_.CurrentAFT.RationalProposalProgram.primary security bits output.val : ℝ) - _root_.CurrentAFT.ProposalPrimary.primaryProfile security output| ≤
      64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * (1 / (2 : ℝ)^bits) := by
  rw [_root_.CurrentAFT.RationalProposalProgram.primary, if_pos (_p2mH180 security bits hprecision hbudget)]
  exact _p2mH181 security bits output hprecision
open _root_.P2Mb608f3c5 renaming h183 → _p2mH183
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h177 (security bits : ℕ) : (_root_.CurrentAFT.RationalProposalProgram.compensationApprox security bits : ℝ) ≤ 1 := by
  apply (_root_.CurrentAFT.RationalProposalProgram.compensationApprox_le_leg_body security bits).trans
  apply (div_le_one (_root_.CurrentAFT.ProposalPrimary.bodySize_pos security)).mpr
  exact_mod_cast (show _root_.CurrentAFT.Parameters.legCount security ≤ _root_.CurrentAFT.Parameters.bodySize security by
    have := _root_.CurrentAFT.ProposalPrimary.population_room security; omega)
open _root_.P2Mb608f3c5 renaming h177 → _p2mH177
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h176 (security bits : ℕ) :
    |(_root_.CurrentAFT.RationalProposalProgram.compensationApprox security bits : ℝ) - _root_.CurrentAFT.ProposalPrimary.compensation security| ≤ (1 / (2 : ℝ)^bits) / 2 := by
  have hfree := _root_.CurrentAFT.ProposalPrimary.freeMass_pos security
  have hLfree : (_root_.CurrentAFT.Parameters.legCount security : ℝ) ≤ _root_.CurrentAFT.ProposalPrimary.freeMass security := by
    have hp := Nat.cast_le (α := ℝ).mpr (_root_.CurrentAFT.ProposalPrimary.population_room security)
    push_cast at hp
    unfold _root_.CurrentAFT.ProposalPrimary.freeMass
    linarith
  have hratio : (_root_.CurrentAFT.Parameters.legCount security : ℝ) / _root_.CurrentAFT.ProposalPrimary.freeMass security ≤ 1 := (div_le_one hfree).mpr hLfree
  rw [_root_.CurrentAFT.RationalProposalProgram.compensationApprox_cast]
  unfold _root_.CurrentAFT.ProposalPrimary.compensation _root_.CurrentAFT.ProposalPrimary.markMass
  have hrewrite : (_root_.CurrentAFT.Parameters.legCount security : ℝ) * _root_.CurrentAFT.LocalPairProgram.activationApprox security bits / _root_.CurrentAFT.ProposalPrimary.freeMass security -
      (_root_.CurrentAFT.Parameters.legCount security : ℝ) * _root_.CurrentAFT.DiffuseProfiles.activation security / _root_.CurrentAFT.ProposalPrimary.freeMass security =
      ((_root_.CurrentAFT.Parameters.legCount security : ℝ) / _root_.CurrentAFT.ProposalPrimary.freeMass security) *
        ((_root_.CurrentAFT.LocalPairProgram.activationApprox security bits : ℝ) - _root_.CurrentAFT.DiffuseProfiles.activation security) := by ring
  rw [hrewrite, abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hfree.le)]
  calc
    _ ≤ ((_root_.CurrentAFT.Parameters.legCount security : ℝ) / _root_.CurrentAFT.ProposalPrimary.freeMass security) *
        ((1 / 2 : ℝ) * (1 / (2 : ℝ)^bits)) :=
      mul_le_mul_of_nonneg_left (_p2mH65 security bits)
        (div_nonneg (Nat.cast_nonneg _) hfree.le)
    _ ≤ 1 * ((1 / 2 : ℝ) * (1 / (2 : ℝ)^bits)) := mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by ring
open _root_.P2Mb608f3c5 renaming h176 → _p2mH176
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h171 (security bits : ℕ) (output : _root_.CurrentAFT.FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (_root_.CurrentAFT.Parameters.base security : ℝ)))
    (hbudget : 64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) :
    |(_root_.CurrentAFT.RationalProposalProgram.anchorPrimary security bits output.val : ℝ) - (_root_.CurrentAFT.ProposalPrimary.anchorPrimaryLaw security).weight output| ≤
      (_root_.CurrentAFT.Parameters.modulus security : ℝ) *
        (64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * (1 / (2 : ℝ)^bits)) +
          1 / (2 : ℝ)^bits := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let error : ℝ := 64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * epsilon
  have hpoint (color : _root_.CurrentAFT.FirstHistogram.Palette security) :
      |(_root_.CurrentAFT.RationalProposalProgram.approximatePrimaryLaw security bits).weight color * (_root_.CurrentAFT.RationalProposalProgram.approximateAnchorLaw security bits color).weight output -
        (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * (_root_.CurrentAFT.InwardAnchor.smoothedAnchorLaw security color).weight output| ≤
          error + (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * epsilon := by
    have hp : |(_root_.CurrentAFT.RationalProposalProgram.approximatePrimaryLaw security bits).weight color - (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color| ≤ error :=
      _p2mH183 security bits color hprecision hbudget
    have hk : |(_root_.CurrentAFT.RationalProposalProgram.approximateAnchorLaw security bits color).weight output -
        (_root_.CurrentAFT.InwardAnchor.smoothedAnchorLaw security color).weight output| ≤ epsilon := by
      rw [← _root_.CurrentAFT.RationalProposalProgram.anchor_cast]
      exact _p2mH172 security bits color output
    calc
      _ = |((_root_.CurrentAFT.RationalProposalProgram.approximatePrimaryLaw security bits).weight color - (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color) *
          (_root_.CurrentAFT.RationalProposalProgram.approximateAnchorLaw security bits color).weight output +
          (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * ((_root_.CurrentAFT.RationalProposalProgram.approximateAnchorLaw security bits color).weight output -
            (_root_.CurrentAFT.InwardAnchor.smoothedAnchorLaw security color).weight output)| := by congr 1; ring
      _ ≤ |(_root_.CurrentAFT.RationalProposalProgram.approximatePrimaryLaw security bits).weight color - (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color| *
          (_root_.CurrentAFT.RationalProposalProgram.approximateAnchorLaw security bits color).weight output +
          (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * |(_root_.CurrentAFT.RationalProposalProgram.approximateAnchorLaw security bits color).weight output -
            (_root_.CurrentAFT.InwardAnchor.smoothedAnchorLaw security color).weight output| := by
        simpa only [abs_mul, abs_of_nonneg (_root_.AFT.FiniteDist.nonneg _ _)] using abs_add_le
          (((_root_.CurrentAFT.RationalProposalProgram.approximatePrimaryLaw security bits).weight color - (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color) *
            (_root_.CurrentAFT.RationalProposalProgram.approximateAnchorLaw security bits color).weight output)
          ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * ((_root_.CurrentAFT.RationalProposalProgram.approximateAnchorLaw security bits color).weight output -
            (_root_.CurrentAFT.InwardAnchor.smoothedAnchorLaw security color).weight output))
      _ ≤ error * 1 + (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * epsilon :=
        add_le_add (mul_le_mul hp ((_root_.CurrentAFT.RationalProposalProgram.approximateAnchorLaw security bits color).atom_le_one output)
          (_root_.AFT.FiniteDist.nonneg _ _) (by dsimp only [error, epsilon]; positivity))
          (mul_le_mul_of_nonneg_left hk ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).nonneg color))
      _ = _ := by ring
  rw [_root_.CurrentAFT.RationalProposalProgram.anchorPrimary_cast]
  change |(∑ color, (_root_.CurrentAFT.RationalProposalProgram.approximatePrimaryLaw security bits).weight color *
    (_root_.CurrentAFT.RationalProposalProgram.approximateAnchorLaw security bits color).weight output) -
    ∑ color, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * (_root_.CurrentAFT.InwardAnchor.smoothedAnchorLaw security color).weight output| ≤ _
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ color, (error + (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * epsilon) :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.sum_mul, _root_.AFT.FiniteDist.sum_one, one_mul]
      rfl
open _root_.P2Mb608f3c5 renaming h171 → _p2mH171
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h175 (security bits : ℕ) (output : _root_.CurrentAFT.FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (_root_.CurrentAFT.Parameters.base security : ℝ)))
    (hbudget : 64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) :
    |(_root_.CurrentAFT.RationalProposalProgram.center security bits output.val : ℝ) - _root_.CurrentAFT.ProposalPrimary.centerProfile security output| ≤
      (64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * _root_.CurrentAFT.Parameters.modulus security + 2) *
        (1 / (2 : ℝ)^bits) := by
  have hcomp := _p2mH176 security bits
  have hanchor := _p2mH171 security bits output hprecision hbudget
  rw [_root_.CurrentAFT.RationalProposalProgram.anchorPrimary_cast] at hanchor
  have hgap : |(_root_.CurrentAFT.ProposalPrimary.safeLaw security).weight output - (_root_.CurrentAFT.ProposalPrimary.anchorPrimaryLaw security).weight output| ≤ 2 := by
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg ((_root_.CurrentAFT.ProposalPrimary.safeLaw security).nonneg output),
        abs_of_nonneg ((_root_.CurrentAFT.ProposalPrimary.anchorPrimaryLaw security).nonneg output)]
      linarith [(_root_.CurrentAFT.ProposalPrimary.safeLaw security).atom_le_one output, (_root_.CurrentAFT.ProposalPrimary.anchorPrimaryLaw security).atom_le_one output])
  rw [_root_.CurrentAFT.RationalProposalProgram.center_cast]
  have hdecompose : _root_.CurrentAFT.RationalProposalProgram.approximateCenterProfile security bits output - _root_.CurrentAFT.ProposalPrimary.centerProfile security output =
      ((_root_.CurrentAFT.RationalProposalProgram.compensationApprox security bits : ℝ) - _root_.CurrentAFT.ProposalPrimary.compensation security) *
        ((_root_.CurrentAFT.ProposalPrimary.safeLaw security).weight output - (_root_.CurrentAFT.ProposalPrimary.anchorPrimaryLaw security).weight output) -
      (_root_.CurrentAFT.RationalProposalProgram.compensationApprox security bits : ℝ) *
        ((_root_.CurrentAFT.RationalProposalProgram.approximateAnchorPrimaryLaw security bits).weight output - (_root_.CurrentAFT.ProposalPrimary.anchorPrimaryLaw security).weight output) := by
    unfold _root_.CurrentAFT.RationalProposalProgram.approximateCenterProfile _root_.CurrentAFT.ProposalPrimary.centerProfile
    ring
  rw [hdecompose]
  calc
    _ ≤ |(_root_.CurrentAFT.RationalProposalProgram.compensationApprox security bits : ℝ) - _root_.CurrentAFT.ProposalPrimary.compensation security| *
        |(_root_.CurrentAFT.ProposalPrimary.safeLaw security).weight output - (_root_.CurrentAFT.ProposalPrimary.anchorPrimaryLaw security).weight output| +
      (_root_.CurrentAFT.RationalProposalProgram.compensationApprox security bits : ℝ) *
        |(_root_.CurrentAFT.RationalProposalProgram.approximateAnchorPrimaryLaw security bits).weight output - (_root_.CurrentAFT.ProposalPrimary.anchorPrimaryLaw security).weight output| := by
      simpa only [abs_mul, abs_of_nonneg (_root_.CurrentAFT.RationalProposalProgram.compensationApprox_nonneg security bits)] using abs_sub
        (((_root_.CurrentAFT.RationalProposalProgram.compensationApprox security bits : ℝ) - _root_.CurrentAFT.ProposalPrimary.compensation security) *
          ((_root_.CurrentAFT.ProposalPrimary.safeLaw security).weight output - (_root_.CurrentAFT.ProposalPrimary.anchorPrimaryLaw security).weight output))
        ((_root_.CurrentAFT.RationalProposalProgram.compensationApprox security bits : ℝ) *
          ((_root_.CurrentAFT.RationalProposalProgram.approximateAnchorPrimaryLaw security bits).weight output - (_root_.CurrentAFT.ProposalPrimary.anchorPrimaryLaw security).weight output))
    _ ≤ ((1 / (2 : ℝ)^bits) / 2) * 2 + 1 *
        ((_root_.CurrentAFT.Parameters.modulus security : ℝ) *
          (64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * (1 / (2 : ℝ)^bits)) +
          1 / (2 : ℝ)^bits) :=
      add_le_add (mul_le_mul hcomp hgap (abs_nonneg _) (by positivity))
        (mul_le_mul (_p2mH177 security bits) hanchor (abs_nonneg _) (by positivity))
    _ = _ := by ring
open _root_.P2Mb608f3c5 renaming h175 → _p2mH175
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h173 (security bits : ℕ) (output : _root_.CurrentAFT.ActualControls.SafePalette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (_root_.CurrentAFT.Parameters.base security : ℝ)))
    (hbudget : 64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) :
    |(_root_.CurrentAFT.RationalProposalProgram.approximateBodyReference security bits).weight output - (_root_.CurrentAFT.ActualControls.bodyReference security).weight output| ≤
      (64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * _root_.CurrentAFT.Parameters.modulus security + 2) *
        (1 / (2 : ℝ)^bits) :=
  _p2mH175 security bits output.val hprecision hbudget
open _root_.P2Mb608f3c5 renaming h173 → _p2mH173
end
open _root_.P2Mb608f3c5 renaming h171 → _p2mH171
open _root_.P2Mb608f3c5 renaming h172 → _p2mH172
open _root_.P2Mb608f3c5 renaming h173 → _p2mH173
open _root_.P2Mb608f3c5 renaming h174 → _p2mH174
open _root_.P2Mb608f3c5 renaming h175 → _p2mH175
open _root_.P2Mb608f3c5 renaming h176 → _p2mH176
open _root_.P2Mb608f3c5 renaming h177 → _p2mH177
open _root_.P2Mb608f3c5 renaming h178 → _p2mH178
open _root_.P2Mb608f3c5 renaming h179 → _p2mH179
open _root_.P2Mb608f3c5 renaming h180 → _p2mH180
open _root_.P2Mb608f3c5 renaming h181 → _p2mH181
open _root_.P2Mb608f3c5 renaming h182 → _p2mH182
open _root_.P2Mb608f3c5 renaming h183 → _p2mH183
open _root_.P2Mb608f3c5 renaming h184 → _p2mH184
open _root_.P2Mb608f3c5 renaming h210 → _p2mH210
end CurrentAFT.RationalProposalProgram
open _root_.P2Mb608f3c5 renaming h171 → _p2mH171
open _root_.P2Mb608f3c5 renaming h172 → _p2mH172
open _root_.P2Mb608f3c5 renaming h173 → _p2mH173
open _root_.P2Mb608f3c5 renaming h174 → _p2mH174
open _root_.P2Mb608f3c5 renaming h175 → _p2mH175
open _root_.P2Mb608f3c5 renaming h176 → _p2mH176
open _root_.P2Mb608f3c5 renaming h177 → _p2mH177
open _root_.P2Mb608f3c5 renaming h178 → _p2mH178
open _root_.P2Mb608f3c5 renaming h179 → _p2mH179
open _root_.P2Mb608f3c5 renaming h180 → _p2mH180
open _root_.P2Mb608f3c5 renaming h181 → _p2mH181
open _root_.P2Mb608f3c5 renaming h182 → _p2mH182
open _root_.P2Mb608f3c5 renaming h183 → _p2mH183
open _root_.P2Mb608f3c5 renaming h184 → _p2mH184
open _root_.P2Mb608f3c5 renaming h210 → _p2mH210
end
open _root_.P2Mb608f3c5 renaming h171 → _p2mH171
open _root_.P2Mb608f3c5 renaming h172 → _p2mH172
open _root_.P2Mb608f3c5 renaming h173 → _p2mH173
open _root_.P2Mb608f3c5 renaming h174 → _p2mH174
open _root_.P2Mb608f3c5 renaming h175 → _p2mH175
open _root_.P2Mb608f3c5 renaming h176 → _p2mH176
open _root_.P2Mb608f3c5 renaming h177 → _p2mH177
open _root_.P2Mb608f3c5 renaming h178 → _p2mH178
open _root_.P2Mb608f3c5 renaming h179 → _p2mH179
open _root_.P2Mb608f3c5 renaming h180 → _p2mH180
open _root_.P2Mb608f3c5 renaming h181 → _p2mH181
open _root_.P2Mb608f3c5 renaming h182 → _p2mH182
open _root_.P2Mb608f3c5 renaming h183 → _p2mH183
open _root_.P2Mb608f3c5 renaming h184 → _p2mH184
namespace CurrentAFT.CurrentGroupSourcePadding
end CurrentAFT.CurrentGroupSourcePadding
namespace CurrentAFT.CurrentGroupSourcePadding.decode
end CurrentAFT.CurrentGroupSourcePadding.decode
namespace CurrentAFT.CurrentGroupSourcePadding.groupKind
end CurrentAFT.CurrentGroupSourcePadding.groupKind
namespace CurrentAFT.GroupSourcePadding
end CurrentAFT.GroupSourcePadding
namespace CurrentAFT.GroupSourcePadding.indexDecode
end CurrentAFT.GroupSourcePadding.indexDecode
section
namespace CurrentAFT.CurrentRootOrdering
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h41 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) :
    (_root_.CurrentAFT.CurrentRootOrdering.keptIndices selection tagged).card ≤ tagged.card := by
  unfold _root_.CurrentAFT.CurrentRootOrdering.keptIndices _root_.CurrentAFT.CurrentRootOrdering.tagIndices _root_.CurrentAFT.CurrentRootOrdering.keptTags
  rw [Finset.card_map]
  exact Finset.card_filter_le _ _
open _root_.P2Mb608f3c5 renaming h41 → _p2mH41
end CurrentAFT.CurrentRootOrdering
open _root_.P2Mb608f3c5 renaming h41 → _p2mH41
end
open _root_.P2Mb608f3c5 renaming h41 → _p2mH41
namespace AFT.MixedKernel.canonicalPointBasis
end AFT.MixedKernel.canonicalPointBasis
namespace CurrentAFT.CanonicalReconstruction.atomProduct_centered
end CurrentAFT.CanonicalReconstruction.atomProduct_centered
namespace CurrentAFT.CanonicalReconstruction.pointTensor
end CurrentAFT.CanonicalReconstruction.pointTensor
namespace CurrentAFT.CompleteRaisingEvaluation
end CurrentAFT.CompleteRaisingEvaluation
namespace CurrentAFT.CompleteRaisingEvaluation.normalizedJoint
end CurrentAFT.CompleteRaisingEvaluation.normalizedJoint
namespace CurrentAFT.CompleteRaisingEvaluation.normalizedSlot
end CurrentAFT.CompleteRaisingEvaluation.normalizedSlot
section
namespace CurrentAFT.PointFamilyProducts
open AFT ControlCoordinates ControlProduct CanonicalReconstruction GradedControlAlgebra BackgroundFamilies
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.PointFamilyProducts.finDecidableEq
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h84 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) {r s r' s' : ℕ}
    (first : Fin r → Primary) (second : Fin r' → Primary)
    (left : Fin s → Body) (right : Fin s' → Body) :
    _root_.CurrentAFT.ControlProduct.finDisjointTensor (_root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body first left) (_root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body second right) =
      _root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body (_root_.CurrentAFT.PointFamilyProducts.append first second) (_root_.CurrentAFT.PointFamilyProducts.append left right) := by
  funext colors centers
  have hp := (finSumFinEquiv : (Fin r ⊕ Fin r') ≃ Fin (r+r')).prod_comp
    (fun index => _root_.AFT.Hoeffding.centeredAtom primary (_root_.CurrentAFT.PointFamilyProducts.append first second index) (colors index))
  have hb := (finSumFinEquiv : (Fin s ⊕ Fin s') ≃ Fin (s+s')).prod_comp
    (fun index => _root_.AFT.Hoeffding.centeredAtom body (_root_.CurrentAFT.PointFamilyProducts.append left right index) (centers index))
  simp only [_root_.CurrentAFT.PointFamilyProducts.append, Equiv.symm_apply_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] at hp hb
  simp only [_root_.CurrentAFT.CanonicalReconstruction.pointTensor, _root_.CurrentAFT.PointFamilyProducts.append, ← hp, ← hb, _root_.CurrentAFT.ControlProduct.finDisjointTensor, _root_.CurrentAFT.ControlProduct.reindexKernel, _root_.CurrentAFT.ControlProduct.disjointTensor,
    Function.comp_apply]
  ring
open _root_.P2Mb608f3c5 renaming h84 → _p2mH84
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h78 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color) {r s r' s' : ℕ}
    (first : Fin r → Primary) (second : Fin r' → Primary)
    (left : Fin s → Body) (right : Fin s' → Body) :
    _root_.CurrentAFT.ControlProduct.homogeneousProduct primary body (_root_.CurrentAFT.CanonicalReconstruction.pointKernel primary body hp hb first left)
      (_root_.CurrentAFT.CanonicalReconstruction.pointKernel primary body hp hb second right) =
      _root_.CurrentAFT.CanonicalReconstruction.pointKernel primary body hp hb (_root_.CurrentAFT.PointFamilyProducts.append first second) (_root_.CurrentAFT.PointFamilyProducts.append left right) := by
  apply Subtype.ext
  change _root_.CurrentAFT.ControlProduct.symmetrize (_root_.CurrentAFT.ControlProduct.finDisjointTensor (_root_.CurrentAFT.ControlProduct.symmetrize (_root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body first left))
    (_root_.CurrentAFT.ControlProduct.symmetrize (_root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body second right))) = _
  rw [_root_.CurrentAFT.ControlProduct.finDisjointTensor, ← _root_.CurrentAFT.ControlProduct.reindexKernel_symmetrize, _root_.CurrentAFT.ControlProduct.symmetrizedTensor_first_symmetrize,
    _root_.CurrentAFT.ControlProduct.symmetrizedTensor_second_symmetrize, _root_.CurrentAFT.ControlProduct.reindexKernel_symmetrize]
  change _root_.CurrentAFT.ControlProduct.symmetrize (_root_.CurrentAFT.ControlProduct.finDisjointTensor (_root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body first left) (_root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body second right)) = _
  rw [_p2mH84]
  rfl
open _root_.P2Mb608f3c5 renaming h78 → _p2mH78
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h80 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) {r s r' s' : ℕ} (h : r+s ≤ order) (h' : r'+s' ≤ order)
    (htotal : (r+r')+(s+s') ≤ order)
    (first : Fin r → Primary) (second : Fin r' → Primary)
    (left : Fin s → Body) (right : Fin s' → Body) :
    _root_.CurrentAFT.PointFamilyProducts.pointFamily primary body hp hb order h first left * _root_.CurrentAFT.PointFamilyProducts.pointFamily primary body hp hb order h' second right =
      _root_.CurrentAFT.PointFamilyProducts.pointFamily primary body hp hb order htotal (_root_.CurrentAFT.PointFamilyProducts.append first second) (_root_.CurrentAFT.PointFamilyProducts.append left right) := by
  change _root_.CurrentAFT.GradedControlAlgebra.familyProduct primary body order (_root_.CurrentAFT.PointFamilyProducts.pointFamily primary body hp hb order h first left)
    (_root_.CurrentAFT.PointFamilyProducts.pointFamily primary body hp hb order h' second right) = _
  unfold _root_.CurrentAFT.PointFamilyProducts.pointFamily
  rw [_root_.CurrentAFT.GradedControlAlgebra.familyProduct_single_retained primary body order _ _ _ _ htotal, _p2mH78]
  rfl
open _root_.P2Mb608f3c5 renaming h80 → _p2mH80
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h81 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color) (order : ℕ)
    (h : 0+0 ≤ order) : _root_.CurrentAFT.PointFamilyProducts.pointFamily primary body hp hb order h Fin.elim0 Fin.elim0 = 1 := by
  have hk : _root_.CurrentAFT.CanonicalReconstruction.pointKernel primary body hp hb (Fin.elim0 : Fin 0 → Primary) (Fin.elim0 : Fin 0 → Body) =
      _root_.CurrentAFT.ControlProduct.scalarUnit primary body := by
    apply Subtype.ext
    change _root_.CurrentAFT.ControlProduct.symmetrize _ = _
    have ht : _root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body (Fin.elim0 : Fin 0 → Primary) (Fin.elim0 : Fin 0 → Body) =
        (_root_.CurrentAFT.ControlProduct.scalarUnit primary body).val := by funext colors centers; simp [_root_.CurrentAFT.CanonicalReconstruction.pointTensor, _root_.CurrentAFT.ControlProduct.scalarUnit]
    rw [ht, _root_.CurrentAFT.ControlProduct.symmetrize_of_symmetric _ (_root_.CurrentAFT.ControlProduct.scalarUnit primary body).property.2.2]
  unfold _root_.CurrentAFT.PointFamilyProducts.pointFamily
  rw [hk]
  rfl
open _root_.P2Mb608f3c5 renaming h81 → _p2mH81
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h83 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (horder : 1 ≤ order) (color : Primary) :
    _root_.CurrentAFT.BackgroundFamilies.primaryFamily primary body order horder (_root_.AFT.Hoeffding.centeredAtom primary color)
      (_root_.AFT.Hoeffding.centeredAtom_mean primary hp color) =
      _root_.CurrentAFT.PointFamilyProducts.pointFamily primary body hp hb order (by omega) (fun _ : Fin 1 => color) Fin.elim0 := by
  have hk : _root_.CurrentAFT.CanonicalReconstruction.pointKernel primary body hp hb (fun _ : Fin 1 => color) (Fin.elim0 : Fin 0 → Body) =
      _root_.CurrentAFT.BackgroundFamilies.primaryKernel primary body (_root_.AFT.Hoeffding.centeredAtom primary color) (_root_.AFT.Hoeffding.centeredAtom_mean primary hp color) := by
    apply Subtype.ext
    have ht : _root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body (fun _ : Fin 1 => color) (Fin.elim0 : Fin 0 → Body) =
        (_root_.CurrentAFT.BackgroundFamilies.primaryKernel primary body (_root_.AFT.Hoeffding.centeredAtom primary color) (_root_.AFT.Hoeffding.centeredAtom_mean primary hp color)).val := by
      funext colors centers
      simp only [_root_.CurrentAFT.CanonicalReconstruction.pointTensor, Fin.prod_univ_one, Fin.prod_univ_zero, mul_one, _root_.CurrentAFT.BackgroundFamilies.primaryKernel]
    change _root_.CurrentAFT.ControlProduct.symmetrize _ = _
    rw [ht, _root_.CurrentAFT.ControlProduct.symmetrize_of_symmetric _ (_root_.CurrentAFT.BackgroundFamilies.primaryKernel primary body _ _).property.2.2]
  unfold _root_.CurrentAFT.BackgroundFamilies.primaryFamily _root_.CurrentAFT.PointFamilyProducts.pointFamily
  rw [hk]
  rfl
open _root_.P2Mb608f3c5 renaming h83 → _p2mH83
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h77 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (horder : 1 ≤ order) (color : Body) :
    _root_.CurrentAFT.BackgroundFamilies.bodyFamily primary body order horder (_root_.AFT.Hoeffding.centeredAtom body color)
      (_root_.AFT.Hoeffding.centeredAtom_mean body hb color) =
      _root_.CurrentAFT.PointFamilyProducts.pointFamily primary body hp hb order (by omega) Fin.elim0 (fun _ : Fin 1 => color) := by
  have hk : _root_.CurrentAFT.CanonicalReconstruction.pointKernel primary body hp hb (Fin.elim0 : Fin 0 → Primary) (fun _ : Fin 1 => color) =
      _root_.CurrentAFT.BackgroundFamilies.bodyKernel primary body (_root_.AFT.Hoeffding.centeredAtom body color) (_root_.AFT.Hoeffding.centeredAtom_mean body hb color) := by
    apply Subtype.ext
    have ht : _root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body (Fin.elim0 : Fin 0 → Primary) (fun _ : Fin 1 => color) =
        (_root_.CurrentAFT.BackgroundFamilies.bodyKernel primary body (_root_.AFT.Hoeffding.centeredAtom body color) (_root_.AFT.Hoeffding.centeredAtom_mean body hb color)).val := by
      funext colors centers
      simp only [_root_.CurrentAFT.CanonicalReconstruction.pointTensor, Fin.prod_univ_one, Fin.prod_univ_zero, one_mul, _root_.CurrentAFT.BackgroundFamilies.bodyKernel]
    change _root_.CurrentAFT.ControlProduct.symmetrize _ = _
    rw [ht, _root_.CurrentAFT.ControlProduct.symmetrize_of_symmetric _ (_root_.CurrentAFT.BackgroundFamilies.bodyKernel primary body _ _).property.2.2]
  unfold _root_.CurrentAFT.BackgroundFamilies.bodyFamily _root_.CurrentAFT.PointFamilyProducts.pointFamily
  rw [hk]
  rfl
open _root_.P2Mb608f3c5 renaming h77 → _p2mH77
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h75 {Color : Type*} {count : ℕ} (word : Fin (count+1) → Color) :
    _root_.CurrentAFT.PointFamilyProducts.append (fun index => word index.castSucc) (fun _ : Fin 1 => word (Fin.last count)) = word := by
  funext index
  obtain ⟨left | right, rfl⟩ := (finSumFinEquiv : (Fin count ⊕ Fin 1) ≃ Fin (count+1)).surjective index
  · simp only [_root_.CurrentAFT.PointFamilyProducts.append, Equiv.symm_apply_apply, Sum.elim_inl]
    congr 1
  · have hr : right = 0 := Subsingleton.elim _ _
    subst right
    simp only [_root_.CurrentAFT.PointFamilyProducts.append, Equiv.symm_apply_apply, Sum.elim_inr]
    congr 1
open _root_.P2Mb608f3c5 renaming h75 → _p2mH75
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h82 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (horder : 1 ≤ order) (count : ℕ) (hcount : count ≤ order) (word : Fin count → Primary) :
    (∏ index, _root_.CurrentAFT.BackgroundFamilies.primaryFamily primary body order horder (_root_.AFT.Hoeffding.centeredAtom primary (word index))
      (_root_.AFT.Hoeffding.centeredAtom_mean primary hp (word index))) =
      _root_.CurrentAFT.PointFamilyProducts.pointFamily primary body hp hb order (by omega) word Fin.elim0 := by
  induction count with
  | zero =>
    have hw : word = Fin.elim0 := Subsingleton.elim _ _
    subst word
    rw [Fin.prod_univ_zero, _p2mH81]
  | succ count ih =>
    rw [Fin.prod_univ_castSucc, ih (by omega), _p2mH83 primary body hp hb]
    rw [_p2mH80 primary body hp hb order _ _ (by omega), _p2mH75]
    congr 1
    funext index
    exact Fin.elim0 (show Fin 0 from index)
open _root_.P2Mb608f3c5 renaming h82 → _p2mH82
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h76 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (horder : 1 ≤ order) (count : ℕ) (hcount : count ≤ order) (word : Fin count → Body) :
    (∏ index, _root_.CurrentAFT.BackgroundFamilies.bodyFamily primary body order horder (_root_.AFT.Hoeffding.centeredAtom body (word index))
      (_root_.AFT.Hoeffding.centeredAtom_mean body hb (word index))) =
      _root_.CurrentAFT.PointFamilyProducts.pointFamily primary body hp hb order (by omega) Fin.elim0 word := by
  induction count with
  | zero =>
    have hw : word = Fin.elim0 := Subsingleton.elim _ _
    subst word
    rw [Fin.prod_univ_zero, _p2mH81]
  | succ count ih =>
    rw [Fin.prod_univ_castSucc, ih (by omega), _p2mH77 primary body hp hb]
    rw [_p2mH80 primary body hp hb order _ _ (by omega), _p2mH75]
    congr 1
    funext index
    exact Fin.elim0 (show Fin 0 from index)
open _root_.P2Mb608f3c5 renaming h76 → _p2mH76
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h79 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) {r s r' s' : ℕ} (h' : r'+s' ≤ order) (hr : r'=r) (hs : s'=s) (h : r+s ≤ order)
    (colors : Fin r' → Primary) (centers : Fin s' → Body) :
    _root_.CurrentAFT.PointFamilyProducts.pointFamily primary body hp hb order h' colors centers =
      _root_.CurrentAFT.PointFamilyProducts.pointFamily primary body hp hb order h (fun index => colors (index.cast hr.symm))
        (fun index => centers (index.cast hs.symm)) := by
  subst r'
  subst s'
  rfl
open _root_.P2Mb608f3c5 renaming h79 → _p2mH79
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h74 {Color : Type*} {count : ℕ} (word : Fin count → Color) (index : Fin count) :
    _root_.CurrentAFT.PointFamilyProducts.append word (Fin.elim0 : Fin 0 → Color) (index.cast (Nat.add_zero count).symm) = word index := by
  have he : index.cast (Nat.add_zero count).symm = finSumFinEquiv (.inl index : Fin count ⊕ Fin 0) := by
    apply Fin.ext
    rfl
  rw [he]
  simp only [_root_.CurrentAFT.PointFamilyProducts.append, Equiv.symm_apply_apply, Sum.elim_inl]
open _root_.P2Mb608f3c5 renaming h74 → _p2mH74
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h73 {Color : Type*} {count : ℕ} (word : Fin count → Color) (index : Fin count) :
    _root_.CurrentAFT.PointFamilyProducts.append (Fin.elim0 : Fin 0 → Color) word (index.cast (Nat.zero_add count).symm) = word index := by
  have he : index.cast (Nat.zero_add count).symm = finSumFinEquiv (.inr index : Fin 0 ⊕ Fin count) := by
    apply Fin.ext
    simp
  rw [he]
  simp only [_root_.CurrentAFT.PointFamilyProducts.append, Equiv.symm_apply_apply, Sum.elim_inr]
open _root_.P2Mb608f3c5 renaming h73 → _p2mH73
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h85 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (horder : 1 ≤ order) {r s : ℕ} (hdegree : r+s ≤ order)
    (colors : Fin r → Primary) (centers : Fin s → Body) :
    (∏ index, _root_.CurrentAFT.BackgroundFamilies.primaryFamily primary body order horder (_root_.AFT.Hoeffding.centeredAtom primary (colors index))
      (_root_.AFT.Hoeffding.centeredAtom_mean primary hp (colors index))) *
    (∏ index, _root_.CurrentAFT.BackgroundFamilies.bodyFamily primary body order horder (_root_.AFT.Hoeffding.centeredAtom body (centers index))
      (_root_.AFT.Hoeffding.centeredAtom_mean body hb (centers index))) =
      _root_.CurrentAFT.PointFamilyProducts.pointFamily primary body hp hb order hdegree colors centers := by
  rw [_p2mH82 primary body hp hb order horder r (by omega),
    _p2mH76 primary body hp hb order horder s (by omega)]
  rw [_p2mH80 primary body hp hb order _ _ (by omega),
    _p2mH79 primary body hp hb order _ (Nat.add_zero r) (Nat.zero_add s) hdegree]
  simp only [_p2mH74, _p2mH73]
open _root_.P2Mb608f3c5 renaming h85 → _p2mH85
end
open _root_.P2Mb608f3c5 renaming h73 → _p2mH73
open _root_.P2Mb608f3c5 renaming h74 → _p2mH74
open _root_.P2Mb608f3c5 renaming h75 → _p2mH75
open _root_.P2Mb608f3c5 renaming h76 → _p2mH76
open _root_.P2Mb608f3c5 renaming h77 → _p2mH77
open _root_.P2Mb608f3c5 renaming h78 → _p2mH78
open _root_.P2Mb608f3c5 renaming h79 → _p2mH79
open _root_.P2Mb608f3c5 renaming h80 → _p2mH80
open _root_.P2Mb608f3c5 renaming h81 → _p2mH81
open _root_.P2Mb608f3c5 renaming h82 → _p2mH82
open _root_.P2Mb608f3c5 renaming h83 → _p2mH83
open _root_.P2Mb608f3c5 renaming h84 → _p2mH84
open _root_.P2Mb608f3c5 renaming h85 → _p2mH85
end CurrentAFT.PointFamilyProducts
open _root_.P2Mb608f3c5 renaming h73 → _p2mH73
open _root_.P2Mb608f3c5 renaming h74 → _p2mH74
open _root_.P2Mb608f3c5 renaming h75 → _p2mH75
open _root_.P2Mb608f3c5 renaming h76 → _p2mH76
open _root_.P2Mb608f3c5 renaming h77 → _p2mH77
open _root_.P2Mb608f3c5 renaming h78 → _p2mH78
open _root_.P2Mb608f3c5 renaming h79 → _p2mH79
open _root_.P2Mb608f3c5 renaming h80 → _p2mH80
open _root_.P2Mb608f3c5 renaming h81 → _p2mH81
open _root_.P2Mb608f3c5 renaming h82 → _p2mH82
open _root_.P2Mb608f3c5 renaming h83 → _p2mH83
open _root_.P2Mb608f3c5 renaming h84 → _p2mH84
open _root_.P2Mb608f3c5 renaming h85 → _p2mH85
end
open _root_.P2Mb608f3c5 renaming h73 → _p2mH73
open _root_.P2Mb608f3c5 renaming h74 → _p2mH74
open _root_.P2Mb608f3c5 renaming h75 → _p2mH75
open _root_.P2Mb608f3c5 renaming h76 → _p2mH76
open _root_.P2Mb608f3c5 renaming h77 → _p2mH77
open _root_.P2Mb608f3c5 renaming h78 → _p2mH78
open _root_.P2Mb608f3c5 renaming h79 → _p2mH79
open _root_.P2Mb608f3c5 renaming h80 → _p2mH80
open _root_.P2Mb608f3c5 renaming h81 → _p2mH81
open _root_.P2Mb608f3c5 renaming h82 → _p2mH82
open _root_.P2Mb608f3c5 renaming h83 → _p2mH83
open _root_.P2Mb608f3c5 renaming h84 → _p2mH84
open _root_.P2Mb608f3c5 renaming h85 → _p2mH85
namespace CurrentAFT.FinitePolynomialTensor
end CurrentAFT.FinitePolynomialTensor
namespace CurrentAFT.FinitePolynomialTensor.synthesis
end CurrentAFT.FinitePolynomialTensor.synthesis
section
namespace CurrentAFT.RootPolynomialTensor
open AFT FinitePolynomialTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootPolynomialTensor.classicalProdDecidableEq
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {RootData Control : Index → Type*} [∀ index, Fintype (RootData index)] [∀ index, Fintype (Control index)]
  {Value : Type*} [CommRing Value] [Algebra ℝ Value]
set_option maxRecDepth 8192
omit [Fintype Index] [DecidableEq Index] [∀ index, Fintype (Control index)] in
theorem _root_.P2Mb608f3c5.h197 (reference : ∀ index, _root_.AFT.FiniteDist (RootData index))
    (physical : ∀ index, RootData index → (Control index → ℝ) →ₗ[ℝ] Value)
    (index : Index) (point : RootData index × Control index) :
    _root_.CurrentAFT.RootPolynomialTensor.averagedChannel reference physical index (Pi.single point 1) =
      (reference index).weight point.1 • physical index point.1 (Pi.single point.2 1) := by
  classical
  rcases point with ⟨pointRoot, pointControl⟩
  simp only [_root_.CurrentAFT.RootPolynomialTensor.averagedChannel, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    _root_.CurrentAFT.RootPolynomialTensor.sliceLinear, LinearMap.coe_mk, AddHom.coe_mk]
  change (∑ root, (reference index).weight root • physical index root
    (fun control => (Pi.single (pointRoot, pointControl) (1 : ℝ) : RootData index × Control index → ℝ) (root, control))) = _
  rw [Finset.sum_eq_single pointRoot]
  · congr 1
    congr 1
    funext control
    simp [Pi.single_apply]
  · intro root _ hne
    have hzero : (fun control => (Pi.single (pointRoot, pointControl) (1 : ℝ) : RootData index × Control index → ℝ) (root, control)) = 0 := by
      funext control
      simp [hne]
    rw [hzero, map_zero, smul_zero]
  · simp
open _root_.P2Mb608f3c5 renaming h197 → _p2mH197
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h198
    (reference : ∀ index, _root_.AFT.FiniteDist (RootData index))
    (physical : ∀ index, RootData index → (Control index → ℝ) →ₗ[ℝ] Value)
    (input : ((index : Index) → RootData index × Control index) → ℝ) :
    _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.RootPolynomialTensor.averagedChannel reference physical) input =
      ∑ roots : (index : Index) → RootData index, (∏ index, (reference index).weight (roots index)) •
        _root_.CurrentAFT.FinitePolynomialTensor.synthesis (fun index => physical index (roots index)) (fun controls => input (fun index => (roots index, controls index))) := by
  unfold _root_.CurrentAFT.FinitePolynomialTensor.synthesis
  simp only [_p2mH197, Finset.prod_smul, smul_smul, Finset.smul_sum]
  rw [← Fintype.sum_prod_type (f := fun pair : ((index : Index) → RootData index) × ((index : Index) → Control index) =>
    ((∏ index, (reference index).weight (pair.1 index)) * input (fun index => (pair.1 index, pair.2 index))) •
      ∏ index, physical index (pair.1 index) (Pi.single (pair.2 index) 1))]
  rw [← (_root_.CurrentAFT.RootPolynomialTensor.sourceEquiv (RootData := RootData) (Control := Control)).sum_comp]
  apply Finset.sum_congr rfl
  intro source _
  simp only [_root_.CurrentAFT.RootPolynomialTensor.sourceEquiv, Equiv.coe_fn_mk]
  rw [mul_comm]
open _root_.P2Mb608f3c5 renaming h198 → _p2mH198
end
open _root_.P2Mb608f3c5 renaming h197 → _p2mH197
open _root_.P2Mb608f3c5 renaming h198 → _p2mH198
end CurrentAFT.RootPolynomialTensor
open _root_.P2Mb608f3c5 renaming h197 → _p2mH197
open _root_.P2Mb608f3c5 renaming h198 → _p2mH198
end
open _root_.P2Mb608f3c5 renaming h197 → _p2mH197
open _root_.P2Mb608f3c5 renaming h198 → _p2mH198
namespace CurrentAFT.RootConditionalComponent
end CurrentAFT.RootConditionalComponent
section
namespace CurrentAFT.RootIndependentSelectedPhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection PairedRootPlacement
  PairedRootInput CycleRootExpansion ControlCoordinates ControlProduct GradedControlAlgebra
  LocalCoefficientFamily RaisingPatternBudget FinitePolynomialTensor
  DiffuseProfiles ProposalPrimary ActualControls CompleteRaisingEvaluation
  RootConditionalComponent
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootIndependentSelectedPhysical.baselineFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentSelectedPhysical.baselineVertexDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentSelectedPhysical.baselineSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentSelectedPhysical.baselineProdDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentSelectedPhysical.baselineSubtypeDecidableEq
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount primaryLaw bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h194 (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ)
    (role : _root_.CurrentAFT.RaisingPatternBudget.Role r s) (source : _root_.CurrentAFT.RaisingPatternBudget.RoleInput security r s role) :
    _root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedRole security order horder r s role (Pi.single source 1) =
      (_root_.CurrentAFT.RaisingPatternBudget.roleReference security r s role).weight source • _root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint security order horder r s role source := by
  cases role with
  | inl index =>
      change _root_.CurrentAFT.RaisingChannels.primaryLeading security order horder (Pi.single source 1) +
        _root_.CurrentAFT.RaisingChannels.primaryRaised security order horder (Pi.single source 1) = _
      rw [_root_.CurrentAFT.RaisingChannels.primaryLeading_single, _root_.CurrentAFT.RaisingChannels.primaryRaised_single, ← smul_add]
      congr 1
      unfold _root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint _root_.CurrentAFT.GlobalRaising.primaryPoint
      change _root_.CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear security order horder (_root_.CurrentAFT.GlobalRaising.primaryAtom security source) +
        (_root_.CurrentAFT.NormalizedLocalPolynomial.independentNormalized security order (_root_.CurrentAFT.GlobalRaising.primaryAtom security source).val -
          _root_.CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear security order horder (_root_.CurrentAFT.GlobalRaising.primaryAtom security source)) = _
      abel
  | inr index =>
      change _root_.CurrentAFT.RaisingChannels.bodyLeading security order horder (Pi.single source 1) +
        _root_.CurrentAFT.RaisingChannels.bodyRaised security order horder (Pi.single source 1) = _
      rw [_root_.CurrentAFT.RaisingChannels.bodyLeading_single, _root_.CurrentAFT.RaisingChannels.bodyRaised_single, ← smul_add]
      exact congrArg (fun value : _root_.CurrentAFT.LocalCoefficientFamily.Family security order => (_root_.CurrentAFT.ActualControls.bodyReference security).weight source • value)
        (_p2mH72 security order horder _ _).symm
open _root_.P2Mb608f3c5 renaming h194 → _p2mH194
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h195 (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedRole security order horder r s) (_root_.CurrentAFT.RaisingPatternKernel.inputJoint security kernel) =
      _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order horder kernel := by
  unfold _root_.CurrentAFT.FinitePolynomialTensor.synthesis
  simp_rw [_p2mH194, Finset.prod_smul, smul_smul]
  rw [← (Equiv.prodPiEquivSumPi (fun _ : Fin r => _root_.CurrentAFT.RootIndependentSelectedPhysical.Palette security)
    (fun _ : Fin s => _root_.CurrentAFT.ActualControls.SafePalette security)).sum_comp, Fintype.sum_prod_type]
  unfold _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint
  apply Finset.sum_congr rfl
  intro colors _
  apply Finset.sum_congr rfl
  intro centers _
  simp only [Fintype.prod_sum_type, _root_.CurrentAFT.RaisingPatternBudget.roleReference, _root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint, _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedSlot,
    Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk,
    Sum.elim_inl, Sum.elim_inr, _root_.CurrentAFT.RaisingPatternBudget.RoleInput, _root_.CurrentAFT.RaisingPatternKernel.inputJoint]
  rw [mul_comm]
open _root_.P2Mb608f3c5 renaming h195 → _p2mH195
set_option maxRecDepth 8192
private theorem _root_.P2Mb608f3c5.h216 (security : ℕ)
    (labels : _root_.CurrentAFT.CycleSelections.Selection (_root_.CurrentAFT.Parameters.bodySize security) 0) (word : Fin 0 → _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security 0 labels word = 1 := by
  unfold _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient _root_.CurrentAFT.CycleSelections.centeredRootDensity
  simp only [Fin.prod_univ_zero, _root_.AFT.FiniteDist.expectation_const]
open _root_.P2Mb608f3c5 renaming h216 → _p2mH216
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h193 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (word : _root_.CurrentAFT.PairedRootInput.GroupInput selection ∅) :
    _root_.CurrentAFT.PairedRootInput.jointInput selection ∅ layout kernel word = _root_.CurrentAFT.PairedRootInput.controlKernel selection ∅ kernel (fun group => (word group).2) := by
  unfold _root_.CurrentAFT.PairedRootInput.jointInput
  have hzero (count : ℕ) (hcount : count = 0)
      (labels : _root_.CurrentAFT.CycleSelections.Selection (_root_.CurrentAFT.Parameters.bodySize security) count) (input : Fin count → _root_.CurrentAFT.CycleRootExpansion.Root security) :
      _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security count labels input = 1 := by
    subst count
    exact _p2mH216 security labels input
  rw [hzero _ Finset.card_empty, one_mul]
open _root_.P2Mb608f3c5 renaming h193 → _p2mH193
set_option maxRecDepth 8192
private def _root_.P2Mb608f3c5.h213 {RootData Control : Type*} [Fintype RootData] (law : _root_.AFT.FiniteDist RootData) :
    ((RootData × Control) → ℝ) →ₗ[ℝ] (Control → ℝ) where
  toFun score control := law.expectation (fun root => score (root, control))
  map_add' first second := by funext control; exact _root_.AFT.FiniteDist.expectation_add _ _ _
  map_smul' scalar score := by funext control; exact _root_.AFT.FiniteDist.expectation_const_mul _ _ _
open _root_.P2Mb608f3c5 renaming h213 → CurrentAFT.RootIndependentSelectedPhysical.meanLinear
open _root_.P2Mb608f3c5 renaming h213 → _p2mH213
set_option maxRecDepth 8192
private theorem _root_.P2Mb608f3c5.h211 {RootData Control Value : Type*} [Fintype RootData] [CommRing Value] [Algebra ℝ Value]
    (law : _root_.AFT.FiniteDist RootData) (channel : (Control → ℝ) →ₗ[ℝ] Value) :
    _root_.CurrentAFT.RootPolynomialTensor.averagedChannel (Index := Unit) (fun _ => law) (fun _ _ => channel) () =
      channel.comp (_p2mH213 law) := by
  apply LinearMap.ext
  intro score
  have hmean : _p2mH213 law score = ∑ root, law.weight root • (fun control => score (root, control)) := by
    funext control
    simp only [_p2mH213, LinearMap.coe_mk, AddHom.coe_mk, _root_.AFT.FiniteDist.expectation,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [_root_.CurrentAFT.RootPolynomialTensor.averagedChannel, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, _root_.CurrentAFT.RootPolynomialTensor.sliceLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hmean, map_sum]
  simp only [map_smul]
open _root_.P2Mb608f3c5 renaming h211 → _p2mH211
set_option maxRecDepth 8192
private def _root_.P2Mb608f3c5.h214 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) :
    (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection ∅) → (_root_.CurrentAFT.PairedRootInput.ControlInput selection ∅ group → ℝ) →ₗ[ℝ] _root_.CurrentAFT.LocalCoefficientFamily.Family security order
  | .inl role => _root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedRole security order horder r s role
  | .inr index => isEmptyElim index
open _root_.P2Mb608f3c5 renaming h214 → CurrentAFT.RootIndependentSelectedPhysical.normalizedActive
open _root_.P2Mb608f3c5 renaming h214 → _p2mH214
set_option maxRecDepth 8192
private theorem _root_.P2Mb608f3c5.h212 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) :
    _root_.CurrentAFT.ActualRootGroupedChannel.channel order horder queue selection ∅ =
      _root_.CurrentAFT.RootPolynomialTensor.averagedChannel
        (_root_.CurrentAFT.RootTaggedPhysicalFactorization.rootReferenceByGroup selection ∅)
        (fun group _ => _p2mH214 order horder selection group) := by
  funext group
  rcases group with (primary | ordinary) | kept
  · apply LinearMap.ext
    intro score
    have hflag : _root_.CurrentAFT.ActualRootGroupedChannel.primaryFlags selection ∅ primary = fun _ => false := by
      funext slot
      simp only [_root_.CurrentAFT.ActualRootGroupedChannel.primaryFlags, Finset.notMem_empty, decide_false]
    change _root_.CurrentAFT.RootPrimaryGroupedChannel.channel security order (_root_.CurrentAFT.ActualRootGroupedChannel.primaryFlags selection ∅ primary) score = _
    rw [hflag, _root_.CurrentAFT.RootPrimaryGroupedChannel.channel_zero,
      _root_.CurrentAFT.RootSelectedZeroTag.zeroChannel_eq_leading_add_raised security order horder]
    exact congrArg (fun map => map score)
      (_p2mH211 (_root_.AFT.FiniteDist.independent (fun _ : Fin 2 => _root_.CurrentAFT.CycleRootExpansion.rootReference security))
        (_root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedRole security order horder r s (.inl primary))).symm
  · apply LinearMap.ext
    intro score
    have hflag : _root_.CurrentAFT.ActualRootGroupedChannel.ordinaryFlag selection ∅ ordinary = false := by
      simp only [_root_.CurrentAFT.ActualRootGroupedChannel.ordinaryFlag, Finset.notMem_empty, decide_false]
    change _root_.CurrentAFT.RootOrdinaryGroupedChannel.channel security order horder (_root_.CurrentAFT.ActualRootGroupedChannel.ordinaryFlag selection ∅ ordinary) score = _
    rw [hflag, _root_.CurrentAFT.RootOrdinaryGroupedChannel.channel_false,
      _p2mH199]
    have hmean : _root_.CurrentAFT.SelectedOrdinaryMean.rootMean security (_root_.CurrentAFT.RootOrdinaryGroupedChannel.toRaw security score) =
        _p2mH213 (_root_.AFT.FiniteDist.independent (fun _ : Fin 1 => _root_.CurrentAFT.CycleRootExpansion.rootReference security)) score := by
      funext center
      exact (_root_.CurrentAFT.RootOrdinaryGroupedChannel.oneRoot_expectation security (fun roots => score (roots, center))).symm
    rw [hmean]
    exact congrArg (fun map => map score)
      (_p2mH211 (_root_.AFT.FiniteDist.independent (fun _ : Fin 1 => _root_.CurrentAFT.CycleRootExpansion.rootReference security))
        (_root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedRole security order horder r s (.inr ordinary))).symm
  · exact isEmptyElim kept
open _root_.P2Mb608f3c5 renaming h212 → CurrentAFT.RootIndependentSelectedPhysical.empty_channel_average
open _root_.P2Mb608f3c5 renaming h212 → _p2mH212
set_option maxRecDepth 8192
private theorem _root_.P2Mb608f3c5.h215 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_p2mH214 order horder selection) (_root_.CurrentAFT.PairedRootInput.controlKernel selection ∅ kernel) =
      _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedRole security order horder r s) (_root_.CurrentAFT.RaisingPatternKernel.inputJoint security kernel) := by
  unfold _root_.CurrentAFT.FinitePolynomialTensor.synthesis _root_.CurrentAFT.PairedRootInput.controlKernel
  rw [← (Equiv.prodPiEquivSumPi (_root_.CurrentAFT.RaisingPatternBudget.RoleInput security r s) (fun _ : _root_.CurrentAFT.PairedRootPlacement.HitKept selection ∅ => Unit)).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.prod_sum_type, _root_.CurrentAFT.PairedRootInput.ControlInput,
    Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk,
    Sum.elim_inl, Sum.elim_inr, _p2mH214, Fintype.prod_empty, mul_one,
    Fintype.sum_unique]
open _root_.P2Mb608f3c5 renaming h215 → _p2mH215
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h196 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.ActualRootResponse.response order horder queue selection ∅ layout kernel = _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order horder kernel := by
  rw [_p2mH29, _root_.CurrentAFT.GroupedFamilyIdentity.response_eq]
  change _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.ActualRootGroupedChannel.channel order horder queue selection ∅)
    (_root_.CurrentAFT.PairedRootInput.jointInput selection ∅ layout kernel) = _
  rw [_p2mH212, _p2mH198]
  simp_rw [_p2mH193]
  rw [← Finset.sum_smul]
  change (∑ roots, (_root_.AFT.FiniteDist.dependentIndependent
    (_root_.CurrentAFT.RootTaggedPhysicalFactorization.rootReferenceByGroup selection ∅)).weight roots) •
      _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_p2mH214 order horder selection) (_root_.CurrentAFT.PairedRootInput.controlKernel selection ∅ kernel) = _
  rw [_root_.AFT.FiniteDist.sum_one, one_smul, _p2mH215, _p2mH195]
open _root_.P2Mb608f3c5 renaming h196 → _p2mH196
end
open _root_.P2Mb608f3c5 renaming h193 → _p2mH193
open _root_.P2Mb608f3c5 renaming h194 → _p2mH194
open _root_.P2Mb608f3c5 renaming h195 → _p2mH195
open _root_.P2Mb608f3c5 renaming h196 → _p2mH196
open _root_.P2Mb608f3c5 renaming h211 → _p2mH211
open _root_.P2Mb608f3c5 renaming h212 → CurrentAFT.RootIndependentSelectedPhysical.empty_channel_average
open _root_.P2Mb608f3c5 renaming h212 → _p2mH212
open _root_.P2Mb608f3c5 renaming h213 → CurrentAFT.RootIndependentSelectedPhysical.meanLinear
open _root_.P2Mb608f3c5 renaming h213 → _p2mH213
open _root_.P2Mb608f3c5 renaming h214 → CurrentAFT.RootIndependentSelectedPhysical.normalizedActive
open _root_.P2Mb608f3c5 renaming h214 → _p2mH214
open _root_.P2Mb608f3c5 renaming h215 → _p2mH215
open _root_.P2Mb608f3c5 renaming h216 → _p2mH216
end CurrentAFT.RootIndependentSelectedPhysical
open _root_.P2Mb608f3c5 renaming h193 → _p2mH193
open _root_.P2Mb608f3c5 renaming h194 → _p2mH194
open _root_.P2Mb608f3c5 renaming h195 → _p2mH195
open _root_.P2Mb608f3c5 renaming h196 → _p2mH196
open _root_.P2Mb608f3c5 renaming h211 → _p2mH211
open _root_.P2Mb608f3c5 renaming h212 → CurrentAFT.RootIndependentSelectedPhysical.empty_channel_average
open _root_.P2Mb608f3c5 renaming h212 → _p2mH212
open _root_.P2Mb608f3c5 renaming h213 → CurrentAFT.RootIndependentSelectedPhysical.meanLinear
open _root_.P2Mb608f3c5 renaming h213 → _p2mH213
open _root_.P2Mb608f3c5 renaming h214 → CurrentAFT.RootIndependentSelectedPhysical.normalizedActive
open _root_.P2Mb608f3c5 renaming h214 → _p2mH214
open _root_.P2Mb608f3c5 renaming h215 → _p2mH215
open _root_.P2Mb608f3c5 renaming h216 → _p2mH216
end
open _root_.P2Mb608f3c5 renaming h193 → _p2mH193
open _root_.P2Mb608f3c5 renaming h194 → _p2mH194
open _root_.P2Mb608f3c5 renaming h195 → _p2mH195
open _root_.P2Mb608f3c5 renaming h196 → _p2mH196
namespace CurrentAFT.ActualRootDefect
end CurrentAFT.ActualRootDefect
namespace CurrentAFT.ActualRootDefect.selectedDefect
end CurrentAFT.ActualRootDefect.selectedDefect
namespace CurrentAFT.ActualRootFamily
end CurrentAFT.ActualRootFamily
namespace CurrentAFT.ActualRootFamily.rootLinear
end CurrentAFT.ActualRootFamily.rootLinear
namespace CurrentAFT.ActualRootFamily.selectedAverage
end CurrentAFT.ActualRootFamily.selectedAverage
section
namespace CurrentAFT.FullResponseEnumeration
open AFT ActualBlockFock ControlCoordinates GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h51 {Pool : Type*} [Fintype Pool] [DecidableEq Pool]
    (order : ℕ) (subset : Finset Pool) : subset ∈ _root_.CurrentAFT.FullResponseEnumeration.boundedSubsets Pool order ↔ subset.card ≤ order := by
  constructor
  · intro hsubset
    obtain ⟨word, _, rfl⟩ := Finset.mem_image.mp hsubset
    have hc := Finset.card_image_le (s := (Finset.univ : Finset (Fin word.1.val))) (f := word.2)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    exact hc.trans (by have := word.1.isLt; omega)
  · intro hcard
    let number : Fin subset.card ≃ subset :=
      (Fintype.equivFinOfCardEq (show Fintype.card subset = subset.card by simp)).symm
    let word : _root_.CurrentAFT.FullResponseEnumeration.SubsetWords Pool order := ⟨⟨subset.card, by omega⟩, fun index => (number index).val⟩
    refine Finset.mem_image.mpr ⟨word, Finset.mem_univ _, ?_⟩
    ext point
    constructor
    · intro hpoint
      obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hpoint
      exact (number index).property
    · intro hpoint
      refine Finset.mem_image.mpr ⟨number.symm ⟨point, hpoint⟩, Finset.mem_univ _, ?_⟩
      exact congrArg Subtype.val (number.apply_symm_apply ⟨point, hpoint⟩)
open _root_.P2Mb608f3c5 renaming h51 → _p2mH51
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h53 {Pool : Type*} [Fintype Pool] (order : ℕ) (hpool : 1 ≤ Fintype.card Pool) :
    Fintype.card (_root_.CurrentAFT.FullResponseEnumeration.SubsetWords Pool order) ≤ (order + 1) * (Fintype.card Pool)^order := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _size : Fin (order + 1), (Fintype.card Pool)^order := by
      apply Finset.sum_le_sum
      intro size _
      simp only [Fintype.card_fun, Fintype.card_fin]
      exact Nat.pow_le_pow_right hpool (by have := size.isLt; omega)
    _ = _ := by simp
open _root_.P2Mb608f3c5 renaming h53 → _p2mH53
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h50 {Pool : Type*} [Fintype Pool] [DecidableEq Pool]
    (order : ℕ) (hpool : 1 ≤ Fintype.card Pool) :
    (_root_.CurrentAFT.FullResponseEnumeration.boundedSubsets Pool order).card ≤ (order + 1) * (Fintype.card Pool)^order := by
  exact (Finset.card_image_le).trans
    ((by simp only [Finset.card_univ] :
      (Finset.univ : Finset (SubsetWords Pool order)).card = Fintype.card (SubsetWords Pool order)).le.trans
      (_p2mH53 order hpool))
open _root_.P2Mb608f3c5 renaming h50 → _p2mH50
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h52 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    _root_.CurrentAFT.ActualRootDefect.selectedDefect order horder queue selection layout =
      ∑ tagged ∈ (_root_.CurrentAFT.FullResponseEnumeration.boundedSubsets (_root_.CurrentAFT.ActualBlockFock.BlockIndex security) order).filter (fun tagged => 2 ≤ tagged.card),
        _root_.CurrentAFT.ActualRootResponse.response order horder queue selection tagged layout := by
  rw [_root_.CurrentAFT.ActualRootDefect.selectedDefect_eq_small]
  have hsets : (Finset.univ : Finset (Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))).filter
      (fun tagged => 2 ≤ tagged.card ∧ tagged.card ≤ order) =
      (_root_.CurrentAFT.FullResponseEnumeration.boundedSubsets (_root_.CurrentAFT.ActualBlockFock.BlockIndex security) order).filter (fun tagged => 2 ≤ tagged.card) := by
    ext tagged
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, _p2mH51, and_comm]
  rw [hsets]
open _root_.P2Mb608f3c5 renaming h52 → _p2mH52
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h49 (security : ℕ) : Fintype.card (_root_.CurrentAFT.ActualBlockFock.BlockIndex security) = _root_.CurrentAFT.Parameters.bodySize security := by
  have hroom := _root_.CurrentAFT.ProposalPrimary.population_room security
  simp only [_root_.CurrentAFT.ActualBlockFock.BlockIndex, Fintype.card_sum, Fintype.card_fin, _root_.CurrentAFT.ActualBlockFock.centerCount]
  omega
open _root_.P2Mb608f3c5 renaming h49 → _p2mH49
end
open _root_.P2Mb608f3c5 renaming h49 → _p2mH49
open _root_.P2Mb608f3c5 renaming h50 → _p2mH50
open _root_.P2Mb608f3c5 renaming h51 → _p2mH51
open _root_.P2Mb608f3c5 renaming h52 → _p2mH52
open _root_.P2Mb608f3c5 renaming h53 → _p2mH53
end CurrentAFT.FullResponseEnumeration
open _root_.P2Mb608f3c5 renaming h49 → _p2mH49
open _root_.P2Mb608f3c5 renaming h50 → _p2mH50
open _root_.P2Mb608f3c5 renaming h51 → _p2mH51
open _root_.P2Mb608f3c5 renaming h52 → _p2mH52
open _root_.P2Mb608f3c5 renaming h53 → _p2mH53
end
open _root_.P2Mb608f3c5 renaming h49 → _p2mH49
open _root_.P2Mb608f3c5 renaming h50 → _p2mH50
open _root_.P2Mb608f3c5 renaming h51 → _p2mH51
open _root_.P2Mb608f3c5 renaming h52 → _p2mH52
open _root_.P2Mb608f3c5 renaming h53 → _p2mH53
namespace CurrentAFT.ActualBlockFock
end CurrentAFT.ActualBlockFock
namespace CurrentAFT.ActualBlockFock.centerCount
end CurrentAFT.ActualBlockFock.centerCount
namespace CurrentAFT.FullResponseEnumeration
end CurrentAFT.FullResponseEnumeration
section
namespace CurrentAFT.FullResponsePointFormula
open AFT ActualControls ProposalPrimary ControlCoordinates ControlProduct CanonicalReconstruction
  GradedControlAlgebra LocalCoefficientFamily ActualCompleteStability
  CalibrationPointCoordinates ActualRootFamily ActualBlockFock
  TaggedSelection UniformTaggedOutput BackgroundRates ActualBackground FullResponseEnumeration
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.FullResponsePointFormula.pointFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  primaryLaw bodyReference ordinaryPool
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h55 (security order : ℕ) (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) :
    _root_.CurrentAFT.CalibrationPointCoordinates.decode (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.ActualControls.primaryReference_positive security)
      (_root_.CurrentAFT.ActualControls.bodyReference_positive security) order (Pi.single source 1) =
        _root_.CurrentAFT.FullResponsePointFormula.referenceWeight security order source • _root_.CurrentAFT.FullResponsePointFormula.basisFamily security order source := by
  rcases source with ⟨sourceArity, sourcePrimary, sourceBody⟩
  funext arity
  by_cases hequal : arity = sourceArity
  · subst arity
    simp [_root_.CurrentAFT.CalibrationPointCoordinates.decode, _root_.CurrentAFT.FullResponsePointFormula.referenceWeight, _root_.CurrentAFT.FullResponsePointFormula.basisFamily, Pi.single_apply, ite_and]
  · have hzero (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
        (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
        (Pi.single (M := fun _ : _root_.CurrentAFT.FullResponsePointFormula.Index security order => ℝ)
          ⟨sourceArity, sourcePrimary, sourceBody⟩ (1 : ℝ)) ⟨arity, colors, centers⟩ = 0 := by
      have hne : (⟨arity, colors, centers⟩ : _root_.CurrentAFT.FullResponsePointFormula.Index security order) ≠
          ⟨sourceArity, sourcePrimary, sourceBody⟩ := fun h => hequal (congrArg Sigma.fst h)
      exact Pi.single_eq_of_ne (M := fun _ : _root_.CurrentAFT.FullResponsePointFormula.Index security order => ℝ) hne (1 : ℝ)
    simp only [_root_.CurrentAFT.CalibrationPointCoordinates.decode, LinearMap.coe_mk, AddHom.coe_mk, hzero, mul_zero, zero_smul,
      Finset.sum_const_zero, Pi.smul_apply, _root_.CurrentAFT.FullResponsePointFormula.basisFamily, Pi.single_eq_of_ne hequal, smul_zero]
open _root_.P2Mb608f3c5 renaming h55 → _p2mH55
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h58 (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) arity.val.1.val arity.val.2.val) :
    _root_.CurrentAFT.ActualRootFamily.rootLinear security order horder hroom queue layout (Pi.single arity kernel) =
      _root_.CurrentAFT.ActualRootFamily.selectedAverage security order horder hroom queue layout arity kernel := by
  rw [_root_.CurrentAFT.ActualRootFamily.rootLinear_apply, Finset.sum_eq_single arity]
  · rw [Pi.single_eq_same]
  · intro other _ hother
    rw [Pi.single_eq_of_ne hother, map_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim
open _root_.P2Mb608f3c5 renaming h58 → _p2mH58
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h57 (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) :
    _root_.CurrentAFT.ActualRootFamily.rootLinear security order horder hroom queue layout (_root_.CurrentAFT.FullResponsePointFormula.basisFamily security order source) =
      _root_.CurrentAFT.FullResponsePointFormula.rootPointResponse security order horder hroom queue layout source := by
  rw [_root_.CurrentAFT.FullResponsePointFormula.basisFamily, _p2mH58, _root_.CurrentAFT.ActualRootFamily.selectedAverage_apply]
  unfold _root_.CurrentAFT.FullResponsePointFormula.rootPointResponse
  apply Finset.sum_congr rfl
  intro choice _
  congr 1
  rw [_p2mH52]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_congr (by ext tagged; simp [_p2mH51])
  intro tagged _
  rfl
open _root_.P2Mb608f3c5 renaming h57 → _p2mH57
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h56 (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) :
    _root_.CurrentAFT.ActualCompleteStability.fullResponse security order horder hroom layout (_root_.CurrentAFT.FullResponsePointFormula.basisFamily security order source) =
      _root_.CurrentAFT.FullResponsePointFormula.pointResponse security order horder hroom layout source := by
  simp only [_root_.CurrentAFT.ActualCompleteStability.fullResponse, LinearMap.add_apply, _root_.CurrentAFT.ActualCompleteStability.independentResponse, _root_.CurrentAFT.ActualCompleteStability.rootCorrection,
    LinearMap.coe_mk, AddHom.coe_mk, _p2mH57, _root_.CurrentAFT.FullResponsePointFormula.pointResponse]
open _root_.P2Mb608f3c5 renaming h56 → _p2mH56
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h54 (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (output source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) :
    _root_.CurrentAFT.CalibrationPointCoordinates.currentMatrix security order horder hsecurity layout output source =
      (if output = source then 1 else 0) -
        _root_.CurrentAFT.FullResponsePointFormula.referenceWeight security order source *
          (_root_.CurrentAFT.FullResponsePointFormula.basisFamily security order source output.1).val output.2.1 output.2.2 +
        _root_.CurrentAFT.FullResponsePointFormula.referenceWeight security order source *
          (_root_.CurrentAFT.FullResponsePointFormula.pointResponse security order horder (_root_.CurrentAFT.ActualCompleteStability.room security order horder hsecurity) layout source output.1).val
            output.2.1 output.2.2 := by
  simp only [_root_.CurrentAFT.CalibrationPointCoordinates.currentMatrix, LinearMap.toMatrix'_apply, _root_.CurrentAFT.CalibrationPointCoordinates.extend, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.comp_apply, _p2mH55, map_smul, _p2mH56, map_sub]
  simp only [_root_.CurrentAFT.CalibrationPointCoordinates.encode, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, Pi.single_apply]
  split_ifs <;> ring
open _root_.P2Mb608f3c5 renaming h54 → _p2mH54
end
open _root_.P2Mb608f3c5 renaming h54 → _p2mH54
open _root_.P2Mb608f3c5 renaming h55 → _p2mH55
open _root_.P2Mb608f3c5 renaming h56 → _p2mH56
open _root_.P2Mb608f3c5 renaming h57 → _p2mH57
open _root_.P2Mb608f3c5 renaming h58 → _p2mH58
end CurrentAFT.FullResponsePointFormula
open _root_.P2Mb608f3c5 renaming h54 → _p2mH54
open _root_.P2Mb608f3c5 renaming h55 → _p2mH55
open _root_.P2Mb608f3c5 renaming h56 → _p2mH56
open _root_.P2Mb608f3c5 renaming h57 → _p2mH57
open _root_.P2Mb608f3c5 renaming h58 → _p2mH58
end
open _root_.P2Mb608f3c5 renaming h54 → _p2mH54
open _root_.P2Mb608f3c5 renaming h55 → _p2mH55
open _root_.P2Mb608f3c5 renaming h56 → _p2mH56
open _root_.P2Mb608f3c5 renaming h57 → _p2mH57
open _root_.P2Mb608f3c5 renaming h58 → _p2mH58
namespace CurrentAFT.CalibrationPointCoordinates.encode
end CurrentAFT.CalibrationPointCoordinates.encode
namespace CurrentAFT.FullResponsePointFormula
end CurrentAFT.FullResponsePointFormula
namespace CurrentAFT.FullResponsePointFormula.basisFamily
end CurrentAFT.FullResponsePointFormula.basisFamily
namespace CurrentAFT.FullResponsePointFormula.pointResponse
end CurrentAFT.FullResponsePointFormula.pointResponse
namespace CurrentAFT.FullResponsePointFormula.referenceWeight
end CurrentAFT.FullResponsePointFormula.referenceWeight
namespace CurrentAFT.FullResponsePointFormula.rootPointResponse
end CurrentAFT.FullResponsePointFormula.rootPointResponse
namespace CurrentAFT.OrdinaryRaising
end CurrentAFT.OrdinaryRaising
namespace CurrentAFT.OrdinaryRaising.normalizedFamily
end CurrentAFT.OrdinaryRaising.normalizedFamily
namespace CurrentAFT.PointFamilyProducts
end CurrentAFT.PointFamilyProducts
namespace CurrentAFT.PointFamilyProducts.append
end CurrentAFT.PointFamilyProducts.append
namespace CurrentAFT.PointFamilyProducts.pointFamily
end CurrentAFT.PointFamilyProducts.pointFamily
namespace CurrentAFT.RaisingPatternBudget
end CurrentAFT.RaisingPatternBudget
namespace CurrentAFT.RaisingPatternBudget.roleReference
end CurrentAFT.RaisingPatternBudget.roleReference
namespace CurrentAFT.RaisingPatternBudget.roleReference.match_1
end CurrentAFT.RaisingPatternBudget.roleReference.match_1
namespace CurrentAFT.RootIndependentSelectedPhysical
end CurrentAFT.RootIndependentSelectedPhysical
namespace CurrentAFT.RootIndependentSelectedPhysical.empty_channel_average
end CurrentAFT.RootIndependentSelectedPhysical.empty_channel_average
namespace CurrentAFT.RootIndependentSelectedPhysical.meanLinear
end CurrentAFT.RootIndependentSelectedPhysical.meanLinear
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedActive
end CurrentAFT.RootIndependentSelectedPhysical.normalizedActive
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedActive.match_1
end CurrentAFT.RootIndependentSelectedPhysical.normalizedActive.match_1
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint
end CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint.match_1
end CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint.match_1
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedRole
end CurrentAFT.RootIndependentSelectedPhysical.normalizedRole
section
namespace CurrentAFT.EmptyRootCoefficientIdentity
open AFT ControlCoordinates ControlProduct CanonicalReconstruction GradedControlAlgebra BackgroundFamilies
  LocalCoefficientFamily ProposalPrimary ActualControls CompleteRaising CompleteRaisingEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.EmptyRootCoefficientIdentity.finDecidableEq
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  primaryLaw bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h45 (security order : ℕ) (horder : 1 ≤ order) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.CompleteRaising.selectedPointProduct security order horder ∅ colors centers =
      Pi.single arity (_root_.CurrentAFT.CanonicalReconstruction.pointKernel (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
        (_root_.CurrentAFT.ActualControls.primaryReference_positive security) (_root_.CurrentAFT.ActualControls.bodyReference_positive security) colors centers) := by
  simp only [_root_.CurrentAFT.CompleteRaising.selectedPointProduct, Finset.notMem_empty, if_false, _root_.CurrentAFT.CompleteRaising.slotLeading, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  change (∏ index, _root_.CurrentAFT.BackgroundFamilies.primaryFamily (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder
    (_root_.AFT.Hoeffding.centeredAtom (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (colors index)) _)*
    (∏ index, _root_.CurrentAFT.BackgroundFamilies.bodyFamily (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder
      (_root_.AFT.Hoeffding.centeredAtom (_root_.CurrentAFT.ActualControls.bodyReference security) (centers index)) _) = _
  exact _p2mH85 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
    (_root_.CurrentAFT.ActualControls.primaryReference_positive security) (_root_.CurrentAFT.ActualControls.bodyReference_positive security) order horder arity.property colors centers
open _root_.P2Mb608f3c5 renaming h45 → _p2mH45
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h44 (security order : ℕ) (horder : 1 ≤ order) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) arity.val.1.val arity.val.2.val) :
    _root_.CurrentAFT.CompleteRaising.selectedCorrection security order horder ∅ kernel = Pi.single arity kernel := by
  unfold _root_.CurrentAFT.CompleteRaising.selectedCorrection
  simp_rw [_p2mH45 security order horder arity]
  funext output
  by_cases he : output=arity
  · subst output
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same]
    exact _p2mH33 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
      (_root_.CurrentAFT.ActualControls.primaryReference_positive security) (_root_.CurrentAFT.ActualControls.bodyReference_positive security) kernel
  · simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_eq_of_ne he, smul_zero, Finset.sum_const_zero]
open _root_.P2Mb608f3c5 renaming h44 → _p2mH44
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h47 (security order : ℕ) (horder : 1 ≤ order) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) arity.val.1.val arity.val.2.val) :
    _root_.CurrentAFT.CompleteRaising.raisingLinear security order horder (Pi.single arity kernel) =
      _root_.CurrentAFT.CompleteRaising.homogeneousCorrectionLinear security order horder arity.val.1.val arity.val.2.val kernel := by
  change (∑ index : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order, _root_.CurrentAFT.CompleteRaising.homogeneousCorrectionLinear security order horder
    index.val.1.val index.val.2.val ((Pi.single arity kernel : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) index)) = _
  rw [Finset.sum_eq_single arity]
  · rw [Pi.single_eq_same]
  · intro index _ hne
    rw [Pi.single_eq_of_ne hne, map_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ arity)).elim
open _root_.P2Mb608f3c5 renaming h47 → _p2mH47
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h46 (security order : ℕ) (horder : 1 ≤ order) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) arity.val.1.val arity.val.2.val) :
    _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order horder kernel =
      Pi.single arity kernel+_root_.CurrentAFT.CompleteRaising.raisingLinear security order horder (Pi.single arity kernel) := by
  rw [_p2mH36, _p2mH44 security order horder arity, _p2mH47]
open _root_.P2Mb608f3c5 renaming h46 → _p2mH46
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h48 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security arity.val.1.val arity.val.2.val)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) arity.val.1.val arity.val.2.val) :
    _root_.CurrentAFT.ActualRootResponse.response order horder queue selection ∅ layout kernel =
      Pi.single arity kernel+_root_.CurrentAFT.CompleteRaising.raisingLinear security order horder (Pi.single arity kernel) := by
  rw [_p2mH196, _p2mH46 security order horder arity]
open _root_.P2Mb608f3c5 renaming h48 → _p2mH48
end
open _root_.P2Mb608f3c5 renaming h44 → _p2mH44
open _root_.P2Mb608f3c5 renaming h45 → _p2mH45
open _root_.P2Mb608f3c5 renaming h46 → _p2mH46
open _root_.P2Mb608f3c5 renaming h47 → _p2mH47
open _root_.P2Mb608f3c5 renaming h48 → _p2mH48
end CurrentAFT.EmptyRootCoefficientIdentity
open _root_.P2Mb608f3c5 renaming h44 → _p2mH44
open _root_.P2Mb608f3c5 renaming h45 → _p2mH45
open _root_.P2Mb608f3c5 renaming h46 → _p2mH46
open _root_.P2Mb608f3c5 renaming h47 → _p2mH47
open _root_.P2Mb608f3c5 renaming h48 → _p2mH48
end
open _root_.P2Mb608f3c5 renaming h44 → _p2mH44
open _root_.P2Mb608f3c5 renaming h45 → _p2mH45
open _root_.P2Mb608f3c5 renaming h46 → _p2mH46
open _root_.P2Mb608f3c5 renaming h47 → _p2mH47
open _root_.P2Mb608f3c5 renaming h48 → _p2mH48
namespace CurrentAFT.RationalDensityInverseProgram
end CurrentAFT.RationalDensityInverseProgram
namespace CurrentAFT.RationalDensityInverseProgram.current
end CurrentAFT.RationalDensityInverseProgram.current
section
namespace CurrentAFT.RationalTensorInverseProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalTensorInverseProgram.classicalFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h191 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalTensorInverseProgram.actualBound security := by
  unfold _root_.CurrentAFT.RationalTensorInverseProgram.actualBound _root_.CurrentAFT.RationalDensityInverseProgram.inverseBound
  positivity
open _root_.P2Mb608f3c5 renaming h191 → _p2mH191
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h192 {Index : Type*} [DecidableEq Index]
    (set : Finset Index) (first second : Index → ℝ) (bound error : ℝ)
    (hb : 1 ≤ bound) (he : 0 ≤ error)
    (hfirst : ∀ index ∈ set, |first index| ≤ bound)
    (hsecond : ∀ index ∈ set, |second index| ≤ bound)
    (hdiff : ∀ index ∈ set, |first index - second index| ≤ error) :
    |(∏ index ∈ set, first index) - ∏ index ∈ set, second index| ≤
      (set.card : ℝ) * error * bound^set.card := by
  classical
  induction set using Finset.induction_on with
  | empty => simp
  | @insert index set hnot ih =>
    have hfirst' := fun other hmem => hfirst other (Finset.mem_insert_of_mem hmem)
    have hsecond' := fun other hmem => hsecond other (Finset.mem_insert_of_mem hmem)
    have hdiff' := fun other hmem => hdiff other (Finset.mem_insert_of_mem hmem)
    have hprod : |∏ other ∈ set, second other| ≤ bound^set.card := by
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _other ∈ set, bound := Finset.prod_le_prod (fun other _ => abs_nonneg _) hsecond'
        _ = _ := by rw [Finset.prod_const]
    have hi := ih hfirst' hsecond' hdiff'
    simp only [Finset.prod_insert hnot, Finset.card_insert_of_notMem hnot, Nat.cast_add, Nat.cast_one]
    calc
      _ = |first index * ((∏ other ∈ set, first other) - ∏ other ∈ set, second other) +
        (first index - second index) * ∏ other ∈ set, second other| := by congr 1; ring
      _ ≤ |first index| * |(∏ other ∈ set, first other) - ∏ other ∈ set, second other| +
          |first index - second index| * |∏ other ∈ set, second other| := by
        simpa only [abs_mul] using abs_add_le
          (first index * ((∏ other ∈ set, first other) - ∏ other ∈ set, second other))
          ((first index - second index) * ∏ other ∈ set, second other)
      _ ≤ bound * ((set.card : ℝ) * error * bound^set.card) + error * bound^set.card :=
        add_le_add (mul_le_mul (hfirst index (Finset.mem_insert_self ..)) hi (abs_nonneg _) (by positivity))
          (mul_le_mul (hdiff index (Finset.mem_insert_self ..)) hprod (abs_nonneg _) he)
      _ ≤ _ := by
        rw [pow_succ]
        have hpow : 0 ≤ bound^set.card := pow_nonneg (by linarith) _
        nlinarith [mul_nonneg he hpow, mul_nonneg (mul_nonneg he hpow) (sub_nonneg.mpr hb)]
open _root_.P2Mb608f3c5 renaming h192 → _p2mH192
end
open _root_.P2Mb608f3c5 renaming h191 → _p2mH191
open _root_.P2Mb608f3c5 renaming h192 → _p2mH192
end CurrentAFT.RationalTensorInverseProgram
open _root_.P2Mb608f3c5 renaming h191 → _p2mH191
open _root_.P2Mb608f3c5 renaming h192 → _p2mH192
end
open _root_.P2Mb608f3c5 renaming h191 → _p2mH191
open _root_.P2Mb608f3c5 renaming h192 → _p2mH192
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalFamilyProductProgram.productFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h105 (r s : ℕ) (value : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℚ) :
    ((_root_.CurrentAFT.RationalFamilyProductProgram.average r s value : ℚ) : ℝ) = _root_.CurrentAFT.RationalFamilyProductProgram.average r s (fun first second => (value first second : ℝ)) := by
  simp only [_root_.CurrentAFT.RationalFamilyProductProgram.average, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum]
open _root_.P2Mb608f3c5 renaming h105 → _p2mH105
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h112 {Primary Body : Type*} {r s r' s' : ℕ}
    (first : _root_.CurrentAFT.RationalFamilyProductProgram.Kernel ℚ Primary Body r s) (second : _root_.CurrentAFT.RationalFamilyProductProgram.Kernel ℚ Primary Body r' s')
    (colors : Fin (r+r') → Primary) (centers : Fin (s+s') → Body) :
    ((_root_.CurrentAFT.RationalFamilyProductProgram.homogeneous first second colors centers : ℚ) : ℝ) =
      _root_.CurrentAFT.RationalFamilyProductProgram.homogeneous (fun colors centers => (first colors centers : ℝ))
        (fun colors centers => (second colors centers : ℝ)) colors centers := by
  rw [_root_.CurrentAFT.RationalFamilyProductProgram.homogeneous, _p2mH105]
  simp only [_root_.CurrentAFT.RationalFamilyProductProgram.tensor, Rat.cast_mul, _root_.CurrentAFT.RationalFamilyProductProgram.homogeneous]
open _root_.P2Mb608f3c5 renaming h112 → _p2mH112
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h120 {Primary Body : Type*} (order : ℕ) (first second : _root_.CurrentAFT.RationalFamilyProductProgram.Table ℚ Primary Body order) :
    _root_.CurrentAFT.RationalFamilyProductProgram.realTable order (_root_.CurrentAFT.RationalFamilyProductProgram.product order first second) = _root_.CurrentAFT.RationalFamilyProductProgram.product order (_root_.CurrentAFT.RationalFamilyProductProgram.realTable order first) (_root_.CurrentAFT.RationalFamilyProductProgram.realTable order second) := by
  funext output colors centers
  simp only [_root_.CurrentAFT.RationalFamilyProductProgram.realTable, _root_.CurrentAFT.RationalFamilyProductProgram.product, Rat.cast_sum]
  apply Finset.sum_congr (by ext left; simp)
  intro left _
  apply Finset.sum_congr (by ext right; simp)
  intro right _
  split_ifs with hmatch
  · exact _p2mH112 (first left) (second right) _ _
  · exact Rat.cast_zero
open _root_.P2Mb608f3c5 renaming h120 → _p2mH120
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h110 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) {r s r' s' : ℕ}
    (first : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r s) (second : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r' s') :
    _root_.CurrentAFT.RationalFamilyProductProgram.homogeneous first.val second.val = (_root_.CurrentAFT.ControlProduct.homogeneousProduct primary body first second).val := by
  funext colors centers
  rw [_p2mH40]
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.homogeneous _root_.CurrentAFT.RationalFamilyProductProgram.average
  apply congrArg (fun total : ℝ => ((r+r').factorial : ℝ)⁻¹ * ((s+s').factorial : ℝ)⁻¹ * total)
  apply Finset.sum_congr (by ext first; simp)
  intro firstOrder _
  apply Finset.sum_congr (by ext second; simp)
  intro secondOrder _
  rfl
open _root_.P2Mb608f3c5 renaming h110 → _p2mH110
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h118 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ)
    (first second : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) :
    _root_.CurrentAFT.RationalFamilyProductProgram.product order (fun arity => (first arity).val) (fun arity => (second arity).val) =
      fun arity => (_root_.CurrentAFT.GradedControlAlgebra.familyProduct primary body order first second arity).val := by
  funext output colors centers
  simp only [_root_.CurrentAFT.RationalFamilyProductProgram.product, _root_.CurrentAFT.GradedControlAlgebra.familyProduct, Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr (by ext left; simp)
  intro left _
  apply Finset.sum_congr (by ext right; simp)
  intro right _
  split_ifs with hmatch
  · rw [_p2mH110, _root_.CurrentAFT.GradedControlAlgebra.transportKernel_val]
    rfl
  · rfl
open _root_.P2Mb608f3c5 renaming h118 → _p2mH118
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h104 (r s : ℕ)
    (value : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℝ) (bound : ℝ)
    (hvalue : ∀ first second, |value first second| ≤ bound) : |_root_.CurrentAFT.RationalFamilyProductProgram.average r s value| ≤ bound := by
  have h := _p2mH30
    ((_root_.AFT.FiniteDist.uniform (Equiv.Perm (Fin r))).prod (_root_.AFT.FiniteDist.uniform (Equiv.Perm (Fin s))))
    (fun pair => value pair.1 pair.2) bound (fun pair => hvalue pair.1 pair.2)
  convert h using 1
  congr 1
  simp only [_root_.CurrentAFT.RationalFamilyProductProgram.average, _root_.AFT.FiniteDist.expectation, _root_.AFT.FiniteDist.prod_weight, _root_.AFT.FiniteDist.uniform_weight,
    Fintype.sum_prod_type, Fintype.card_perm, Fintype.card_fin, ← Finset.mul_sum]
  apply congrArg (fun total : ℝ => (r.factorial : ℝ)⁻¹ * (s.factorial : ℝ)⁻¹ * total)
  apply Finset.sum_congr (by ext first; simp)
  intro first _
  apply Finset.sum_congr (by ext second; simp)
  intro second _
  rfl
open _root_.P2Mb608f3c5 renaming h104 → _p2mH104
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h106 (r s : ℕ) (first second : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℝ) :
    _root_.CurrentAFT.RationalFamilyProductProgram.average r s first - _root_.CurrentAFT.RationalFamilyProductProgram.average r s second = _root_.CurrentAFT.RationalFamilyProductProgram.average r s (fun p b => first p b - second p b) := by
  simp only [_root_.CurrentAFT.RationalFamilyProductProgram.average, Finset.sum_sub_distrib, mul_sub]
open _root_.P2Mb608f3c5 renaming h106 → _p2mH106
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h114 (first second computedFirst computedSecond A B e f : ℝ)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (he : 0 ≤ e) (_hf : 0 ≤ f)
    (ha : |first| ≤ A) (hb : |second| ≤ B)
    (hea : |computedFirst-first| ≤ e) (heb : |computedSecond-second| ≤ f) :
    |computedFirst*computedSecond-first*second| ≤ e*B + (A+e)*f := by
  have hcomputed : |computedFirst| ≤ A+e := by
    have h := abs_add_le first (computedFirst-first)
    rw [add_sub_cancel] at h
    exact h.trans (add_le_add ha hea)
  have hequal : computedFirst*computedSecond-first*second =
      (computedFirst-first)*second + computedFirst*(computedSecond-second) := by ring
  rw [hequal]
  exact (abs_add_le _ _).trans (by
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul hea hb (abs_nonneg _) he)
      (mul_le_mul hcomputed heb (abs_nonneg _) (add_nonneg hA he)))
open _root_.P2Mb608f3c5 renaming h114 → _p2mH114
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h111 {Primary Body : Type*} {r s r' s' : ℕ}
    (first : _root_.CurrentAFT.RationalFamilyProductProgram.Kernel ℝ Primary Body r s) (second : _root_.CurrentAFT.RationalFamilyProductProgram.Kernel ℝ Primary Body r' s')
    (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (ha : ∀ colors centers, |first colors centers| ≤ A)
    (hb : ∀ colors centers, |second colors centers| ≤ B)
    (colors : Fin (r+r') → Primary) (centers : Fin (s+s') → Body) :
    |_root_.CurrentAFT.RationalFamilyProductProgram.homogeneous first second colors centers| ≤ A*B := by
  apply _p2mH104
  intro p b
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.tensor
  rw [abs_mul]
  exact mul_le_mul (ha _ _) (hb _ _) (abs_nonneg _) hA
open _root_.P2Mb608f3c5 renaming h111 → _p2mH111
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h113 {Primary Body : Type*} {r s r' s' : ℕ}
    (first computedFirst : _root_.CurrentAFT.RationalFamilyProductProgram.Kernel ℝ Primary Body r s) (second computedSecond : _root_.CurrentAFT.RationalFamilyProductProgram.Kernel ℝ Primary Body r' s')
    (A B e f : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hf : 0 ≤ f)
    (ha : ∀ colors centers, |first colors centers| ≤ A)
    (hb : ∀ colors centers, |second colors centers| ≤ B)
    (hea : ∀ colors centers, |computedFirst colors centers-first colors centers| ≤ e)
    (heb : ∀ colors centers, |computedSecond colors centers-second colors centers| ≤ f)
    (colors : Fin (r+r') → Primary) (centers : Fin (s+s') → Body) :
    |_root_.CurrentAFT.RationalFamilyProductProgram.homogeneous computedFirst computedSecond colors centers - _root_.CurrentAFT.RationalFamilyProductProgram.homogeneous first second colors centers| ≤
      e*B + (A+e)*f := by
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.homogeneous
  rw [_p2mH106]
  apply _p2mH104
  intro p b
  exact _p2mH114 _ _ _ _ A B e f hA hB he hf (ha _ _) (hb _ _) (hea _ _) (heb _ _)
open _root_.P2Mb608f3c5 renaming h113 → _p2mH113
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h121 {Primary Body : Type*} (order : ℕ)
    (first computedFirst second computedSecond : _root_.CurrentAFT.RationalFamilyProductProgram.Table ℝ Primary Body order)
    (A B e f : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hf : 0 ≤ f)
    (ha : ∀ arity colors centers, |first arity colors centers| ≤ A)
    (hb : ∀ arity colors centers, |second arity colors centers| ≤ B)
    (hea : ∀ arity colors centers, |computedFirst arity colors centers-first arity colors centers| ≤ e)
    (heb : ∀ arity colors centers, |computedSecond arity colors centers-second arity colors centers| ≤ f)
    (output : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin output.val.1.val → Primary)
    (centers : Fin output.val.2.val → Body) :
    |_root_.CurrentAFT.RationalFamilyProductProgram.product order computedFirst computedSecond output colors centers - _root_.CurrentAFT.RationalFamilyProductProgram.product order first second output colors centers| ≤
      (Fintype.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) : ℝ)^2 * (e*B + (A+e)*f) := by
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.product
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _left : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order, ∑ _right : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order, (e*B + (A+e)*f) := by
      apply Finset.sum_le_sum
      intro left _
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro right _
      split_ifs with hmatch
      · exact _p2mH113 _ _ _ _ A B e f hA hB he hf (ha left) (hb right) (hea left) (heb right) _ _
      · simp only [sub_self, abs_zero]
        positivity
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
open _root_.P2Mb608f3c5 renaming h121 → _p2mH121
end
open _root_.P2Mb608f3c5 renaming h104 → _p2mH104
open _root_.P2Mb608f3c5 renaming h105 → _p2mH105
open _root_.P2Mb608f3c5 renaming h106 → _p2mH106
open _root_.P2Mb608f3c5 renaming h110 → _p2mH110
open _root_.P2Mb608f3c5 renaming h111 → _p2mH111
open _root_.P2Mb608f3c5 renaming h112 → _p2mH112
open _root_.P2Mb608f3c5 renaming h113 → _p2mH113
open _root_.P2Mb608f3c5 renaming h114 → _p2mH114
open _root_.P2Mb608f3c5 renaming h118 → _p2mH118
open _root_.P2Mb608f3c5 renaming h120 → _p2mH120
open _root_.P2Mb608f3c5 renaming h121 → _p2mH121
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2Mb608f3c5 renaming h104 → _p2mH104
open _root_.P2Mb608f3c5 renaming h105 → _p2mH105
open _root_.P2Mb608f3c5 renaming h106 → _p2mH106
open _root_.P2Mb608f3c5 renaming h110 → _p2mH110
open _root_.P2Mb608f3c5 renaming h111 → _p2mH111
open _root_.P2Mb608f3c5 renaming h112 → _p2mH112
open _root_.P2Mb608f3c5 renaming h113 → _p2mH113
open _root_.P2Mb608f3c5 renaming h114 → _p2mH114
open _root_.P2Mb608f3c5 renaming h118 → _p2mH118
open _root_.P2Mb608f3c5 renaming h120 → _p2mH120
open _root_.P2Mb608f3c5 renaming h121 → _p2mH121
end
open _root_.P2Mb608f3c5 renaming h104 → _p2mH104
open _root_.P2Mb608f3c5 renaming h105 → _p2mH105
open _root_.P2Mb608f3c5 renaming h106 → _p2mH106
open _root_.P2Mb608f3c5 renaming h110 → _p2mH110
open _root_.P2Mb608f3c5 renaming h111 → _p2mH111
open _root_.P2Mb608f3c5 renaming h112 → _p2mH112
open _root_.P2Mb608f3c5 renaming h113 → _p2mH113
open _root_.P2Mb608f3c5 renaming h114 → _p2mH114
open _root_.P2Mb608f3c5 renaming h118 → _p2mH118
open _root_.P2Mb608f3c5 renaming h120 → _p2mH120
open _root_.P2Mb608f3c5 renaming h121 → _p2mH121
namespace AFT.RationalNumerics.HeightBound
end AFT.RationalNumerics.HeightBound
namespace CurrentAFT.RationalFamilyProductProgram
end CurrentAFT.RationalFamilyProductProgram
namespace CurrentAFT.RationalFamilyProductProgram.average
end CurrentAFT.RationalFamilyProductProgram.average
namespace CurrentAFT.RationalFamilyProductProgram.homogeneous
end CurrentAFT.RationalFamilyProductProgram.homogeneous
namespace CurrentAFT.RationalFamilyProductProgram.product
end CurrentAFT.RationalFamilyProductProgram.product
namespace CurrentAFT.RationalFamilyProductProgram.realTable
end CurrentAFT.RationalFamilyProductProgram.realTable
namespace CurrentAFT.RationalFamilyProductProgram.tensor
end CurrentAFT.RationalFamilyProductProgram.tensor
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT RationalNumerics GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h119 {Primary Body : Type*} (order : ℕ)
    (first second : _root_.CurrentAFT.RationalFamilyProductProgram.Table ℝ Primary Body order) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ arity colors centers, |first arity colors centers| ≤ A)
    (hb : ∀ arity colors centers, |second arity colors centers| ≤ B)
    (output : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin output.val.1.val → Primary)
    (centers : Fin output.val.2.val → Body) :
    |_root_.CurrentAFT.RationalFamilyProductProgram.product order first second output colors centers| ≤
      (Fintype.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) : ℝ)^2 * (A*B) := by
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.product
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _left : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order, ∑ _right : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order, (A*B) := by
      apply Finset.sum_le_sum
      intro left _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro right _
      split_ifs with hmatch
      · exact _p2mH111 _ _ A B hA hB (ha left) (hb right) _ _
      · simpa only [abs_zero] using mul_nonneg hA hB
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
open _root_.P2Mb608f3c5 renaming h119 → _p2mH119
end
open _root_.P2Mb608f3c5 renaming h119 → _p2mH119
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2Mb608f3c5 renaming h119 → _p2mH119
end
open _root_.P2Mb608f3c5 renaming h119 → _p2mH119
namespace CurrentAFT.GradedInverse
end CurrentAFT.GradedInverse
namespace CurrentAFT.GradedInverse.backgroundInverse
end CurrentAFT.GradedInverse.backgroundInverse
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalFamilyProductProgram.powerFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h123 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ) :
    _root_.CurrentAFT.RationalFamilyProductProgram.unit (Scalar := ℝ) (Primary := Primary) (Body := Body) order =
      fun arity => ((1 : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) arity).val := by
  funext arity colors centers
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.unit
  change _ = ((_root_.CurrentAFT.GradedControlAlgebra.familyUnit primary body order) arity).val colors centers
  by_cases heq : arity = _root_.CurrentAFT.GradedControlAlgebra.zeroArity order
  · subst arity
    simp only [_root_.CurrentAFT.GradedControlAlgebra.familyUnit, Pi.single_eq_same, if_true, _root_.CurrentAFT.ControlProduct.scalarUnit]
  · simp only [_root_.CurrentAFT.GradedControlAlgebra.familyUnit, Pi.single_eq_of_ne heq, heq, if_false, Submodule.coe_zero, Pi.zero_apply]
open _root_.P2Mb608f3c5 renaming h123 → _p2mH123
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h115 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order count : ℕ)
    (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) :
    _root_.CurrentAFT.RationalFamilyProductProgram.power order (fun arity => (family arity).val) count = fun arity => ((family^count) arity).val := by
  induction count with
  | zero => exact _p2mH123 primary body order
  | succ count ih =>
      rw [_root_.CurrentAFT.RationalFamilyProductProgram.power, ih, _p2mH118, pow_succ]
      rfl
open _root_.P2Mb608f3c5 renaming h115 → _p2mH115
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h117 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ)
    (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) (hzero : family (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0)
    (count : ℕ) (hcount : order < count) : family^count = 0 := by
  have h := _p2mH64 primary body order family
    (_root_.CurrentAFT.GradedInverse.vanishesBelow_one_of_zero primary body order family hzero) count
  funext arity
  exact h arity (by have := arity.property; omega)
open _root_.P2Mb608f3c5 renaming h117 → _p2mH117
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h108 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order population : ℕ)
    (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) (hzero : family (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0) :
    (1 + family)^population =
      ∑ count ∈ Finset.range (order+1), population.choose count • family^count := by
  have hfull : (1 + family)^population =
      ∑ count ∈ Finset.range (population+1), population.choose count • family^count := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro count _
    rw [one_pow, mul_one, nsmul_eq_mul, mul_comm]
  rw [hfull]
  by_cases hle : population ≤ order
  · apply Finset.sum_subset (Finset.range_mono (by omega))
    intro count _ hnot
    have hlarge : population < count := by
      simp only [Finset.mem_range, not_lt] at hnot
      omega
    rw [Nat.choose_eq_zero_of_lt hlarge, zero_nsmul]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro count _ hnot
    have hlarge : order < count := by
      simp only [Finset.mem_range, not_lt] at hnot
      omega
    rw [_p2mH117 primary body order family hzero count hlarge, smul_zero]
open _root_.P2Mb608f3c5 renaming h108 → _p2mH108
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h107 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order population : ℕ)
    (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) (hzero : family (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0) :
    _root_.CurrentAFT.RationalFamilyProductProgram.binomial order population (fun arity => (family arity).val) =
      fun arity => (((1 + family)^population) arity).val := by
  rw [_p2mH108 primary body order population family hzero]
  funext arity colors centers
  simp only [_root_.CurrentAFT.RationalFamilyProductProgram.binomial, _p2mH115, Finset.sum_apply, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro count _
  change _ = population.choose count • (((family^count) arity).val colors centers)
  rw [nsmul_eq_mul]
open _root_.P2Mb608f3c5 renaming h107 → _p2mH107
end
open _root_.P2Mb608f3c5 renaming h107 → _p2mH107
open _root_.P2Mb608f3c5 renaming h108 → _p2mH108
open _root_.P2Mb608f3c5 renaming h115 → _p2mH115
open _root_.P2Mb608f3c5 renaming h117 → _p2mH117
open _root_.P2Mb608f3c5 renaming h123 → _p2mH123
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2Mb608f3c5 renaming h107 → _p2mH107
open _root_.P2Mb608f3c5 renaming h108 → _p2mH108
open _root_.P2Mb608f3c5 renaming h115 → _p2mH115
open _root_.P2Mb608f3c5 renaming h117 → _p2mH117
open _root_.P2Mb608f3c5 renaming h123 → _p2mH123
end
open _root_.P2Mb608f3c5 renaming h107 → _p2mH107
open _root_.P2Mb608f3c5 renaming h108 → _p2mH108
open _root_.P2Mb608f3c5 renaming h115 → _p2mH115
open _root_.P2Mb608f3c5 renaming h117 → _p2mH117
open _root_.P2Mb608f3c5 renaming h123 → _p2mH123
namespace CurrentAFT.RationalTensorInverseProgram
end CurrentAFT.RationalTensorInverseProgram
namespace CurrentAFT.RationalTensorInverseProgram.entry
end CurrentAFT.RationalTensorInverseProgram.entry
namespace CurrentAFT.RootTaggedLocal
end CurrentAFT.RootTaggedLocal
namespace CurrentAFT.RootTaggedLocal.deviationProfile
end CurrentAFT.RootTaggedLocal.deviationProfile
namespace CurrentAFT.RootTaggedLocal.meanLaw
end CurrentAFT.RootTaggedLocal.meanLaw
namespace CurrentAFT.RootTaggedLocal.rootCost
end CurrentAFT.RootTaggedLocal.rootCost
namespace CurrentAFT.RootTaggedLocal.rootMass
end CurrentAFT.RootTaggedLocal.rootMass
namespace CurrentAFT.RootTaggedLocal.shiftedLaw
end CurrentAFT.RootTaggedLocal.shiftedLaw
section
namespace CurrentAFT.RationalMassLiftProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h147 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalMassLiftProgram.errorConstant security := by
  unfold _root_.CurrentAFT.RationalMassLiftProgram.errorConstant _root_.CurrentAFT.RationalDensityInverseProgram.inverseBound _root_.CurrentAFT.RationalFirstResponseProgram.inverseErrorConstant
  positivity
open _root_.P2Mb608f3c5 renaming h147 → _p2mH147
end
open _root_.P2Mb608f3c5 renaming h147 → _p2mH147
end CurrentAFT.RationalMassLiftProgram
open _root_.P2Mb608f3c5 renaming h147 → _p2mH147
end
open _root_.P2Mb608f3c5 renaming h147 → _p2mH147
namespace CurrentAFT.RationalSelectedRootProgram
end CurrentAFT.RationalSelectedRootProgram
namespace CurrentAFT.RootReferenceColumns
end CurrentAFT.RootReferenceColumns
namespace CurrentAFT.RootReferenceColumns.ordinaryAt
end CurrentAFT.RootReferenceColumns.ordinaryAt
namespace CurrentAFT.RootReferenceColumns.ordinaryDensityAt
end CurrentAFT.RootReferenceColumns.ordinaryDensityAt
namespace CurrentAFT.RootReferenceColumns.ordinaryFiber
end CurrentAFT.RootReferenceColumns.ordinaryFiber
namespace CurrentAFT.RootReferenceColumns.reducedColumn
end CurrentAFT.RootReferenceColumns.reducedColumn
namespace CurrentAFT.RootReferenceColumns.singletonDensityAt
end CurrentAFT.RootReferenceColumns.singletonDensityAt
namespace CurrentAFT.RootReferenceColumns.unselectedAt
end CurrentAFT.RootReferenceColumns.unselectedAt
namespace CurrentAFT.SelectedOrdinaryMean.constantRoot
end CurrentAFT.SelectedOrdinaryMean.constantRoot
namespace CurrentAFT.SelectedOrdinaryMean.rootMean
end CurrentAFT.SelectedOrdinaryMean.rootMean
namespace CurrentAFT.SelectedOrdinaryRoot
end CurrentAFT.SelectedOrdinaryRoot
namespace CurrentAFT.SelectedOrdinaryRoot.channel
end CurrentAFT.SelectedOrdinaryRoot.channel
section
namespace CurrentAFT.RationalPrimaryColumnProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalPrimaryColumnProgram.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPrimaryColumnProgram.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h168 (security bits : ℕ) (source color : _root_.CurrentAFT.ActualControls.Palette security) :
    (_root_.CurrentAFT.RationalPrimaryColumnProgram.centerDelta security bits source.val color.val : ℝ) =
      (if color = source then (1 : ℝ) else 0) -
        (_root_.CurrentAFT.RationalProposalProgram.approximatePrimaryLaw security bits).weight source := by
  unfold _root_.CurrentAFT.RationalPrimaryColumnProgram.centerDelta
  by_cases hequal : color = source
  · subst color
    simp only [if_true, Rat.cast_sub, Rat.cast_one]
    rfl
  · have hne : color.val ≠ source.val := fun h => hequal (Fin.ext h)
    simp only [if_neg hne, if_neg hequal, Rat.cast_sub, Rat.cast_zero]
    rfl
open _root_.P2Mb608f3c5 renaming h168 → _p2mH168
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h165 (security : ℕ) (source color : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (Pi.single source 1) color =
      (if color = source then (1 : ℝ) else 0) - (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight source := by
  change (Pi.single (M := fun _ : _root_.CurrentAFT.ActualControls.Palette security => ℝ) source 1) color -
    (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).expectation (Pi.single source 1) = _
  simp [Pi.single_apply, _root_.AFT.FiniteDist.expectation]
open _root_.P2Mb608f3c5 renaming h165 → _p2mH165
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h167 (security bits : ℕ) (source color : _root_.CurrentAFT.ActualControls.Palette security) :
    |(_root_.CurrentAFT.RationalPrimaryColumnProgram.centerDelta security bits source.val color.val : ℝ)| ≤ 1 := by
  rw [_p2mH168]
  have hlo := (_root_.CurrentAFT.RationalProposalProgram.approximatePrimaryLaw security bits).nonneg source
  have hhi := (_root_.CurrentAFT.RationalProposalProgram.approximatePrimaryLaw security bits).atom_le_one source
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2Mb608f3c5 renaming h167 → _p2mH167
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h166 (security : ℕ) (source color : _root_.CurrentAFT.ActualControls.Palette security) :
    |_root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (Pi.single source 1) color| ≤ 1 := by
  rw [_p2mH165]
  have hlo := (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).nonneg source
  have hhi := (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).atom_le_one source
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2Mb608f3c5 renaming h166 → _p2mH166
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h169 (security bits : ℕ) (source color : _root_.CurrentAFT.ActualControls.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (_root_.CurrentAFT.Parameters.base security : ℝ)))
    (hbudget : 64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) :
    |(_root_.CurrentAFT.RationalPrimaryColumnProgram.centerDelta security bits source.val color.val : ℝ) -
      _root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (Pi.single source 1) color| ≤
        _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH168, _p2mH165]
  have h : |(_root_.CurrentAFT.RationalProposalProgram.approximatePrimaryLaw security bits).weight source -
      (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight source| ≤
      _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits) := by
    simpa only [_root_.CurrentAFT.RationalProposalProgram.approximatePrimaryLaw, _root_.CurrentAFT.ProposalPrimary.primaryLaw, _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant] using
      _p2mH183 security bits source hprecision hbudget
  have hequal : ((if color = source then (1 : ℝ) else 0) -
      (_root_.CurrentAFT.RationalProposalProgram.approximatePrimaryLaw security bits).weight source) -
      ((if color = source then (1 : ℝ) else 0) - (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight source) =
        (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight source - (_root_.CurrentAFT.RationalProposalProgram.approximatePrimaryLaw security bits).weight source := by ring
  rw [hequal, abs_sub_comm]
  exact h
open _root_.P2Mb608f3c5 renaming h169 → _p2mH169
end
open _root_.P2Mb608f3c5 renaming h165 → _p2mH165
open _root_.P2Mb608f3c5 renaming h166 → _p2mH166
open _root_.P2Mb608f3c5 renaming h167 → _p2mH167
open _root_.P2Mb608f3c5 renaming h168 → _p2mH168
open _root_.P2Mb608f3c5 renaming h169 → _p2mH169
end CurrentAFT.RationalPrimaryColumnProgram
open _root_.P2Mb608f3c5 renaming h165 → _p2mH165
open _root_.P2Mb608f3c5 renaming h166 → _p2mH166
open _root_.P2Mb608f3c5 renaming h167 → _p2mH167
open _root_.P2Mb608f3c5 renaming h168 → _p2mH168
open _root_.P2Mb608f3c5 renaming h169 → _p2mH169
end
open _root_.P2Mb608f3c5 renaming h165 → _p2mH165
open _root_.P2Mb608f3c5 renaming h166 → _p2mH166
open _root_.P2Mb608f3c5 renaming h167 → _p2mH167
open _root_.P2Mb608f3c5 renaming h168 → _p2mH168
open _root_.P2Mb608f3c5 renaming h169 → _p2mH169
namespace CurrentAFT.RationalFamilyProductProgram.binomial
end CurrentAFT.RationalFamilyProductProgram.binomial
namespace CurrentAFT.RationalFamilyProductProgram.power
end CurrentAFT.RationalFamilyProductProgram.power
namespace CurrentAFT.RationalFamilyProductProgram.power.match_1
end CurrentAFT.RationalFamilyProductProgram.power.match_1
namespace CurrentAFT.RationalFamilyProductProgram.reciprocal
end CurrentAFT.RationalFamilyProductProgram.reciprocal
namespace CurrentAFT.RationalFamilyProductProgram.unit
end CurrentAFT.RationalFamilyProductProgram.unit
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h124 {Primary Body : Type*} (order : ℕ) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (colors : Fin arity.val.1.val → Primary) (centers : Fin arity.val.2.val → Body) :
    |_root_.CurrentAFT.RationalFamilyProductProgram.unit (Scalar := ℝ) order arity colors centers| ≤ 1 := by
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.unit
  split_ifs <;> norm_num
open _root_.P2Mb608f3c5 renaming h124 → _p2mH124
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h116 {Primary Body : Type*} (order : ℕ) (table : _root_.CurrentAFT.RationalFamilyProductProgram.Table ℝ Primary Body order)
    (bound scale : ℝ) (hb : 0 ≤ bound) (hs : 1 ≤ scale)
    (hscale : (Nat.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) : ℝ)^2 * bound ≤ scale)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound) (count : ℕ)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |_root_.CurrentAFT.RationalFamilyProductProgram.power order table count arity colors centers| ≤ scale^count := by
  induction count generalizing arity colors centers with
  | zero => simpa only [_root_.CurrentAFT.RationalFamilyProductProgram.power, pow_zero] using _p2mH124 order arity colors centers
  | succ count ih =>
      have h := _p2mH119 order (_root_.CurrentAFT.RationalFamilyProductProgram.power order table count) table (scale^count) bound
        (pow_nonneg (by linarith) _) hb ih htable arity colors centers
      simp only [Fintype.card_eq_nat_card] at h
      apply h.trans
      have hm := mul_le_mul_of_nonneg_left hscale (pow_nonneg (by linarith : 0 ≤ scale) count)
      rw [pow_succ scale count]
      convert hm using 1
      ring
open _root_.P2Mb608f3c5 renaming h116 → _p2mH116
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h109 (order : ℕ) (bound error : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) :
    1 ≤ _root_.CurrentAFT.RationalFamilyProductProgram.growth order bound error := by
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.growth
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (by positivity))
open _root_.P2Mb608f3c5 renaming h109 → _p2mH109
end
open _root_.P2Mb608f3c5 renaming h109 → _p2mH109
open _root_.P2Mb608f3c5 renaming h116 → _p2mH116
open _root_.P2Mb608f3c5 renaming h124 → _p2mH124
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2Mb608f3c5 renaming h109 → _p2mH109
open _root_.P2Mb608f3c5 renaming h116 → _p2mH116
open _root_.P2Mb608f3c5 renaming h124 → _p2mH124
end
open _root_.P2Mb608f3c5 renaming h109 → _p2mH109
open _root_.P2Mb608f3c5 renaming h116 → _p2mH116
open _root_.P2Mb608f3c5 renaming h124 → _p2mH124
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
variable {Scalar Primary Body Primary' Body' : Type*}
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h122 [Field Scalar] (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
    (first second : _root_.CurrentAFT.RationalFamilyProductProgram.Table Scalar Primary Body order) :
    _root_.CurrentAFT.RationalFamilyProductProgram.pullback order primary body (_root_.CurrentAFT.RationalFamilyProductProgram.product order first second) =
      _root_.CurrentAFT.RationalFamilyProductProgram.product order (_root_.CurrentAFT.RationalFamilyProductProgram.pullback order primary body first) (_root_.CurrentAFT.RationalFamilyProductProgram.pullback order primary body second) := by
  funext arity colors centers
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.pullback _root_.CurrentAFT.RationalFamilyProductProgram.product
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  split_ifs <;> rfl
open _root_.P2Mb608f3c5 renaming h122 → _p2mH122
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2Mb608f3c5 renaming h122 → _p2mH122
end
open _root_.P2Mb608f3c5 renaming h122 → _p2mH122
namespace CurrentAFT.ActualCoordinateBounds
end CurrentAFT.ActualCoordinateBounds
section
namespace CurrentAFT.RationalActualFamilyApproximation
open AFT GradedControlAlgebra ActualControls BackgroundFamilies
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalActualFamilyApproximation.approximationFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h87 (security order : ℕ)
    (first second : _root_.CurrentAFT.RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    _root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (_root_.CurrentAFT.RationalFamilyProductProgram.product order first second) =
      _root_.CurrentAFT.RationalFamilyProductProgram.product order (_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order first) (_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order second) := by
  unfold _root_.CurrentAFT.RationalActualFamilyApproximation.interpret
  rw [_p2mH120, _p2mH122]
open _root_.P2Mb608f3c5 renaming h87 → _p2mH87
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h86 (security order : ℕ) (first second : _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order) :
    _root_.CurrentAFT.RationalFamilyProductProgram.product order (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order first) (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order second) =
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.GradedControlAlgebra.familyProduct (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
        (_root_.CurrentAFT.ActualControls.bodyReference security) order first second) :=
  _p2mH118 _ _ _ _ _
open _root_.P2Mb608f3c5 renaming h86 → _p2mH86
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h88 (security order : ℕ) (family : _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order) (bound : ℝ)
    (hbound : _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order family ≤ bound)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order family arity colors centers| ≤ _root_.CurrentAFT.RationalActualFamilyApproximation.coordinateFactor security order*bound := by
  exact (_p2mH27 security order family arity colors centers).trans
    (mul_le_mul_of_nonneg_left hbound (by positivity))
open _root_.P2Mb608f3c5 renaming h88 → _p2mH88
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h89 (order : ℕ) (A B e f : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hf : 0 ≤ f) :
    0 ≤ _root_.CurrentAFT.RationalActualFamilyApproximation.productError order A B e f := by
  unfold _root_.CurrentAFT.RationalActualFamilyApproximation.productError
  positivity
open _root_.P2Mb608f3c5 renaming h89 → _p2mH89
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h90 (security bits order : ℕ)
    (first second : _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order)
    (computedFirst computedSecond : _root_.CurrentAFT.RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (A B e f : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hf : 0 ≤ f)
    (ha : ∀ arity colors centers, |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order first arity colors centers| ≤ A)
    (hb : ∀ arity colors centers, |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order second arity colors centers| ≤ B)
    (hea : ∀ arity colors centers,
      |_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order computedFirst arity colors centers-_root_.CurrentAFT.RationalActualFamilyApproximation.data security order first arity colors centers| ≤ e*(1/(2:ℝ)^bits))
    (heb : ∀ arity colors centers,
      |_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order computedSecond arity colors centers-_root_.CurrentAFT.RationalActualFamilyApproximation.data security order second arity colors centers| ≤ f*(1/(2:ℝ)^bits))
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (_root_.CurrentAFT.RationalFamilyProductProgram.product order computedFirst computedSecond) arity colors centers-
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.GradedControlAlgebra.familyProduct (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
        (_root_.CurrentAFT.ActualControls.bodyReference security) order first second) arity colors centers| ≤
      _root_.CurrentAFT.RationalActualFamilyApproximation.productError order A B e f*(1/(2:ℝ)^bits) := by
  have hε : (0:ℝ) ≤ 1/2^bits := by positivity
  have hε1 : 1/(2:ℝ)^bits ≤ 1 :=
    (div_le_one (by positivity : (0:ℝ)<2^bits)).mpr (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  rw [_p2mH87, ← _p2mH86]
  have h := _p2mH121 order
    (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order first) (_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order computedFirst)
    (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order second) (_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order computedSecond)
    A B (e*(1/(2:ℝ)^bits)) (f*(1/(2:ℝ)^bits)) hA hB
    (mul_nonneg he hε) (mul_nonneg hf hε) ha hb hea heb arity colors centers
  apply h.trans
  calc
    _ ≤ (Fintype.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order):ℝ)^2*
        ((e*(1/(2:ℝ)^bits))*B+(A+e)*(f*(1/(2:ℝ)^bits))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hAe : A+e*(1/(2:ℝ)^bits) ≤ A+e := by
        nlinarith [mul_le_mul_of_nonneg_left hε1 he]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hAe (mul_nonneg hf hε))
    _ = _ := by unfold _root_.CurrentAFT.RationalActualFamilyApproximation.productError; ring
open _root_.P2Mb608f3c5 renaming h90 → _p2mH90
end
open _root_.P2Mb608f3c5 renaming h86 → _p2mH86
open _root_.P2Mb608f3c5 renaming h87 → _p2mH87
open _root_.P2Mb608f3c5 renaming h88 → _p2mH88
open _root_.P2Mb608f3c5 renaming h89 → _p2mH89
open _root_.P2Mb608f3c5 renaming h90 → _p2mH90
end CurrentAFT.RationalActualFamilyApproximation
open _root_.P2Mb608f3c5 renaming h86 → _p2mH86
open _root_.P2Mb608f3c5 renaming h87 → _p2mH87
open _root_.P2Mb608f3c5 renaming h88 → _p2mH88
open _root_.P2Mb608f3c5 renaming h89 → _p2mH89
open _root_.P2Mb608f3c5 renaming h90 → _p2mH90
end
open _root_.P2Mb608f3c5 renaming h86 → _p2mH86
open _root_.P2Mb608f3c5 renaming h87 → _p2mH87
open _root_.P2Mb608f3c5 renaming h88 → _p2mH88
open _root_.P2Mb608f3c5 renaming h89 → _p2mH89
open _root_.P2Mb608f3c5 renaming h90 → _p2mH90
namespace CurrentAFT.RationalPrimaryColumnProgram
end CurrentAFT.RationalPrimaryColumnProgram
section
namespace CurrentAFT.WeightedPointKernelProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CanonicalReconstruction
  ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.WeightedPointKernelProgram.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.WeightedPointKernelProgram.safeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw bodyReference
section Generic
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h206 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    {r s : ℕ} (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    ((∏ index, primary.weight (sourcePrimary index)) * (∏ index, body.weight (sourceBody index))) •
      (_root_.CurrentAFT.CanonicalReconstruction.pointKernel primary body hp hb sourcePrimary sourceBody).val =
        _root_.CurrentAFT.ControlProduct.symmetrize (_root_.CurrentAFT.WeightedPointKernelProgram.weightedTensor primary body sourcePrimary sourceBody) := by
  have hraw : ((∏ index, primary.weight (sourcePrimary index)) * (∏ index, body.weight (sourceBody index))) •
      _root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body sourcePrimary sourceBody = _root_.CurrentAFT.WeightedPointKernelProgram.weightedTensor primary body sourcePrimary sourceBody := by
    funext colors centers
    simp only [Pi.smul_apply, smul_eq_mul, _root_.CurrentAFT.CanonicalReconstruction.pointTensor, _root_.CurrentAFT.WeightedPointKernelProgram.weightedTensor]
    rw [← _p2mH35 primary hp, ← _p2mH35 body hb]
    ring
  have h := congrArg (_root_.CurrentAFT.ControlProduct.symmetrizeLinear (Primary := Primary) (Body := Body)) hraw
  rw [map_smul] at h
  exact h
open _root_.P2Mb608f3c5 renaming h206 → _p2mH206
end Generic
open _root_.P2Mb608f3c5 renaming h206 → _p2mH206
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h201 (security : ℕ) {r s : ℕ} (sourcePrimary : Fin r → _root_.CurrentAFT.ActualControls.Palette security)
    (sourceBody : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) (colors : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    (_root_.CurrentAFT.WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody).val colors centers =
      _root_.CurrentAFT.RationalFamilyProductProgram.average r s (fun primaryOrder bodyOrder =>
        (∏ index, ((if colors (primaryOrder index) = sourcePrimary index then (1 : ℝ) else 0) -
          (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight (sourcePrimary index))) *
        ∏ index, ((if centers (bodyOrder index) = sourceBody index then (1 : ℝ) else 0) -
          (_root_.CurrentAFT.ActualControls.bodyReference security).weight (sourceBody index))) := by
  have h := congrFun (congrFun (_p2mH206 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
    (_root_.CurrentAFT.ActualControls.primaryReference_positive security) (_root_.CurrentAFT.ActualControls.bodyReference_positive security) sourcePrimary sourceBody) colors) centers
  change (_root_.CurrentAFT.WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody).val colors centers = _ at h
  rw [_root_.CurrentAFT.ControlProduct.symmetrize_apply] at h
  simp only [Fintype.card_perm, Fintype.card_fin, _root_.CurrentAFT.WeightedPointKernelProgram.weightedTensor, _root_.AFT.MixedKernel.canonicalPointBasis] at h
  rw [h]
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.average
  apply congrArg (fun total : ℝ => (r.factorial : ℝ)⁻¹ * (s.factorial : ℝ)⁻¹ * total)
  apply Finset.sum_congr (by ext; simp)
  intro primaryOrder _
  apply Finset.sum_congr (by ext; simp)
  intro bodyOrder _
  try dsimp only
  apply congrArg₂ (fun first second : ℝ => first * second)
  · apply Finset.prod_congr (by ext; simp)
    intro index _
    by_cases hequal : colors (primaryOrder index) = sourcePrimary index <;>
      simp only [Function.comp_apply, hequal, if_true, if_false]
  · apply Finset.prod_congr (by ext; simp)
    intro index _
    by_cases hequal : centers (bodyOrder index) = sourceBody index <;>
      simp only [Function.comp_apply, hequal, if_true, if_false]
open _root_.P2Mb608f3c5 renaming h201 → _p2mH201
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h203 (security bits : ℕ) (source color : _root_.CurrentAFT.ActualControls.SafePalette security) :
    (_root_.CurrentAFT.WeightedPointKernelProgram.bodyDelta security bits source.val.val color.val.val : ℝ) =
      (if color = source then (1 : ℝ) else 0) -
        (_root_.CurrentAFT.RationalProposalProgram.approximateBodyReference security bits).weight source := by
  unfold _root_.CurrentAFT.WeightedPointKernelProgram.bodyDelta
  by_cases hequal : color = source
  · subst color
    simp only [if_true, Rat.cast_sub, Rat.cast_one]
    rfl
  · have hne : color.val.val ≠ source.val.val := fun h => hequal (Subtype.ext (Fin.ext h))
    simp only [if_neg hne, if_neg hequal, Rat.cast_sub, Rat.cast_zero]
    rfl
open _root_.P2Mb608f3c5 renaming h203 → _p2mH203
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h202 (security bits : ℕ) (source color : _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.WeightedPointKernelProgram.bodyDelta security bits source.val.val color.val.val : ℝ)| ≤ 1 := by
  rw [_p2mH203]
  have hlo := (_root_.CurrentAFT.RationalProposalProgram.approximateBodyReference security bits).nonneg source
  have hhi := (_root_.CurrentAFT.RationalProposalProgram.approximateBodyReference security bits).atom_le_one source
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2Mb608f3c5 renaming h202 → _p2mH202
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h204 (security bits : ℕ) (source color : _root_.CurrentAFT.ActualControls.SafePalette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (_root_.CurrentAFT.Parameters.base security : ℝ)))
    (hbudget : 64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) :
    |(_root_.CurrentAFT.WeightedPointKernelProgram.bodyDelta security bits source.val.val color.val.val : ℝ) -
      ((if color = source then (1 : ℝ) else 0) - (_root_.CurrentAFT.ActualControls.bodyReference security).weight source)| ≤
      (_root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant security * _root_.CurrentAFT.Parameters.modulus security + 2) * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH203]
  have h := _p2mH173 security bits source hprecision hbudget
  have hequal : ((if color = source then (1 : ℝ) else 0) -
      (_root_.CurrentAFT.RationalProposalProgram.approximateBodyReference security bits).weight source) -
      ((if color = source then (1 : ℝ) else 0) - (_root_.CurrentAFT.ActualControls.bodyReference security).weight source) =
        (_root_.CurrentAFT.ActualControls.bodyReference security).weight source - (_root_.CurrentAFT.RationalProposalProgram.approximateBodyReference security bits).weight source := by ring
  rw [hequal, abs_sub_comm]
  exact h
open _root_.P2Mb608f3c5 renaming h204 → _p2mH204
set_option maxRecDepth 8192
private theorem _root_.P2Mb608f3c5.h217 {Index : Type} [Fintype Index] (value : Index → ℝ)
    (hvalue : ∀ index, |value index| ≤ 1) : |∏ index, value index| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun index _ => hvalue index)
open _root_.P2Mb608f3c5 renaming h217 → _p2mH217
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h205 (security bits r s : ℕ) (sourcePrimary : Fin r → _root_.CurrentAFT.ActualControls.Palette security)
    (sourceBody : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (_root_.CurrentAFT.Parameters.base security : ℝ)))
    (hbudget : 64 * (_root_.CurrentAFT.Parameters.base security : ℝ) * _root_.CurrentAFT.Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)))
    (colors : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.WeightedPointKernelProgram.current security bits r s (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)
        (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (_root_.CurrentAFT.WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody).val colors centers| ≤
      _root_.CurrentAFT.WeightedPointKernelProgram.errorConstant security r s * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let Cp := _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant security
  let Cb : ℝ := Cp * _root_.CurrentAFT.Parameters.modulus security + 2
  have he : 0 ≤ epsilon := by positivity
  have hp : 0 ≤ Cp := by unfold Cp _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant; positivity
  have hb : 0 ≤ Cb := by dsimp only [Cb]; positivity
  rw [_root_.CurrentAFT.WeightedPointKernelProgram.current, _p2mH105, _p2mH201,
    _p2mH106]
  apply _p2mH104
  intro primaryOrder bodyOrder
  simp only [Rat.cast_mul, Rat.cast_prod]
  let a : Fin r → ℝ := fun index =>
    (_root_.CurrentAFT.RationalPrimaryColumnProgram.centerDelta security bits (sourcePrimary index).val (colors (primaryOrder index)).val : ℝ)
  let b : Fin s → ℝ := fun index =>
    (_root_.CurrentAFT.WeightedPointKernelProgram.bodyDelta security bits (sourceBody index).val.val (centers (bodyOrder index)).val.val : ℝ)
  let x : Fin r → ℝ := fun index => (if colors (primaryOrder index) = sourcePrimary index then 1 else 0) -
    (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight (sourcePrimary index)
  let y : Fin s → ℝ := fun index => (if centers (bodyOrder index) = sourceBody index then 1 else 0) -
    (_root_.CurrentAFT.ActualControls.bodyReference security).weight (sourceBody index)
  have ha (index : Fin r) : |a index| ≤ 1 := _p2mH167 security bits _ _
  have hb' (index : Fin s) : |b index| ≤ 1 := _p2mH202 security bits _ _
  have hx (index : Fin r) : |x index| ≤ 1 := by
    simpa only [_p2mH165] using
      _p2mH166 security (sourcePrimary index) (colors (primaryOrder index))
  have hy (index : Fin s) : |y index| ≤ 1 := by
    have hlo := (_root_.CurrentAFT.ActualControls.bodyReference security).nonneg (sourceBody index)
    have hhi := (_root_.CurrentAFT.ActualControls.bodyReference security).atom_le_one (sourceBody index)
    dsimp only [y]
    split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  have haprod := _p2mH192 Finset.univ a x 1 (Cp * epsilon)
    (by norm_num) (by positivity) (fun index _ => ha index) (fun index _ => hx index)
    (fun index _ => by
      simpa only [_p2mH165] using
        _p2mH169 security bits (sourcePrimary index) (colors (primaryOrder index)) hprecision hbudget)
  have hbprod := _p2mH192 Finset.univ b y 1 (Cb * epsilon)
    (by norm_num) (by positivity) (fun index _ => hb' index) (fun index _ => hy index)
    (fun index _ => _p2mH204 security bits _ _ hprecision hbudget)
  simp only [Finset.card_univ, Fintype.card_fin, one_pow, mul_one] at haprod hbprod
  change |(∏ index, a index) * (∏ index, b index) - (∏ index, x index) * (∏ index, y index)| ≤ _
  calc
    _ = |((∏ index, a index) - ∏ index, x index) * (∏ index, b index) +
      (∏ index, x index) * ((∏ index, b index) - ∏ index, y index)| := by congr 1; ring
    _ ≤ |(∏ index, a index) - ∏ index, x index| * |∏ index, b index| +
      |∏ index, x index| * |(∏ index, b index) - ∏ index, y index| := by
        simpa only [abs_mul] using abs_add_le
          (((∏ index, a index) - ∏ index, x index) * (∏ index, b index))
          ((∏ index, x index) * ((∏ index, b index) - ∏ index, y index))
    _ ≤ ((r : ℝ) * (Cp * epsilon)) * 1 + 1 * ((s : ℝ) * (Cb * epsilon)) :=
      add_le_add (mul_le_mul haprod (_p2mH217 b hb') (abs_nonneg _) (by positivity))
        (mul_le_mul (_p2mH217 x hx) hbprod (abs_nonneg _) (by norm_num))
    _ = _ := by unfold _root_.CurrentAFT.WeightedPointKernelProgram.errorConstant; dsimp only [Cp, Cb, epsilon]; ring
open _root_.P2Mb608f3c5 renaming h205 → CurrentAFT.WeightedPointKernelProgram.current_error
open _root_.P2Mb608f3c5 renaming h205 → _p2mH205
end
open _root_.P2Mb608f3c5 renaming h201 → _p2mH201
open _root_.P2Mb608f3c5 renaming h202 → _p2mH202
open _root_.P2Mb608f3c5 renaming h203 → _p2mH203
open _root_.P2Mb608f3c5 renaming h204 → _p2mH204
open _root_.P2Mb608f3c5 renaming h205 → CurrentAFT.WeightedPointKernelProgram.current_error
open _root_.P2Mb608f3c5 renaming h205 → _p2mH205
open _root_.P2Mb608f3c5 renaming h206 → _p2mH206
open _root_.P2Mb608f3c5 renaming h217 → _p2mH217
end CurrentAFT.WeightedPointKernelProgram
open _root_.P2Mb608f3c5 renaming h201 → _p2mH201
open _root_.P2Mb608f3c5 renaming h202 → _p2mH202
open _root_.P2Mb608f3c5 renaming h203 → _p2mH203
open _root_.P2Mb608f3c5 renaming h204 → _p2mH204
open _root_.P2Mb608f3c5 renaming h205 → CurrentAFT.WeightedPointKernelProgram.current_error
open _root_.P2Mb608f3c5 renaming h205 → _p2mH205
open _root_.P2Mb608f3c5 renaming h206 → _p2mH206
open _root_.P2Mb608f3c5 renaming h217 → _p2mH217
end
open _root_.P2Mb608f3c5 renaming h201 → _p2mH201
open _root_.P2Mb608f3c5 renaming h202 → _p2mH202
open _root_.P2Mb608f3c5 renaming h203 → _p2mH203
open _root_.P2Mb608f3c5 renaming h204 → _p2mH204
open _root_.P2Mb608f3c5 renaming h205 → CurrentAFT.WeightedPointKernelProgram.current_error
open _root_.P2Mb608f3c5 renaming h205 → _p2mH205
open _root_.P2Mb608f3c5 renaming h206 → _p2mH206
namespace CurrentAFT.ActualRootProjectionData
end CurrentAFT.ActualRootProjectionData
namespace CurrentAFT.ActualRootProjectionData.unprojectedChannel
end CurrentAFT.ActualRootProjectionData.unprojectedChannel
namespace CurrentAFT.RationalOrdinaryFamilyProgram
end CurrentAFT.RationalOrdinaryFamilyProgram
namespace CurrentAFT.RationalOrdinaryFamilyProgram.current
end CurrentAFT.RationalOrdinaryFamilyProgram.current
namespace CurrentAFT.RootReferenceColumns.hybridAt
end CurrentAFT.RootReferenceColumns.hybridAt
namespace CurrentAFT.RootWeightedSynthesis
end CurrentAFT.RootWeightedSynthesis
namespace CurrentAFT.RootWeightedSynthesis.taggedOutput
end CurrentAFT.RootWeightedSynthesis.taggedOutput
namespace CurrentAFT.RootWeightedSynthesis.untaggedWeight
end CurrentAFT.RootWeightedSynthesis.untaggedWeight
namespace CurrentAFT.RootWeightedSynthesis.weightedCoefficient
end CurrentAFT.RootWeightedSynthesis.weightedCoefficient
namespace CurrentAFT.SelectedOrdinaryHybrid
end CurrentAFT.SelectedOrdinaryHybrid
namespace CurrentAFT.SelectedOrdinaryHybrid.independentChannel
end CurrentAFT.SelectedOrdinaryHybrid.independentChannel
section
namespace CurrentAFT.RationalRootGroupProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalRootGroupProgram.groupProgramFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw rootReference PublicParameterProgram.modulus
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h185 (security order : ℕ) : 0 ≤ _root_.CurrentAFT.RationalRootGroupProgram.errorConstant security order := by unfold _root_.CurrentAFT.RationalRootGroupProgram.errorConstant; positivity
open _root_.P2Mb608f3c5 renaming h185 → _p2mH185
end
open _root_.P2Mb608f3c5 renaming h185 → _p2mH185
end CurrentAFT.RationalRootGroupProgram
open _root_.P2Mb608f3c5 renaming h185 → _p2mH185
end
open _root_.P2Mb608f3c5 renaming h185 → _p2mH185
namespace CurrentAFT.PrimaryDeviationCertificate
end CurrentAFT.PrimaryDeviationCertificate
namespace CurrentAFT.PrimaryDeviationCertificate.deviation
end CurrentAFT.PrimaryDeviationCertificate.deviation
namespace CurrentAFT.RationalMassCertificateTable
end CurrentAFT.RationalMassCertificateTable
section
namespace CurrentAFT.RationalPrimaryDeviationProgram
open AFT RationalNumerics GradedControlAlgebra ActualControls DiffuseProfiles ProposalPrimary
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalPrimaryDeviationProgram.deviationFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h170 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalPrimaryDeviationProgram.errorConstant security := by
  simp only [_root_.CurrentAFT.RationalPrimaryDeviationProgram.errorConstant, _root_.CurrentAFT.RationalPrimaryDeviationProgram.profileErrorConstant, _root_.CurrentAFT.RationalMassLiftProgram.errorConstant,
    _root_.CurrentAFT.RationalTensorInverseProgram.actualBound, _root_.CurrentAFT.RationalDensityInverseProgram.inverseBound,
    _root_.CurrentAFT.RationalFirstResponseProgram.inverseErrorConstant]
  positivity
open _root_.P2Mb608f3c5 renaming h170 → _p2mH170
end
open _root_.P2Mb608f3c5 renaming h170 → _p2mH170
end CurrentAFT.RationalPrimaryDeviationProgram
open _root_.P2Mb608f3c5 renaming h170 → _p2mH170
end
open _root_.P2Mb608f3c5 renaming h170 → _p2mH170
namespace CurrentAFT.MarkedPairSeed
end CurrentAFT.MarkedPairSeed
namespace CurrentAFT.MarkedPairSeed.uniformRelative
end CurrentAFT.MarkedPairSeed.uniformRelative
namespace CurrentAFT.RationalMarkedSeedProgram
end CurrentAFT.RationalMarkedSeedProgram
namespace CurrentAFT.RationalMarkedSeedProgram.primaryErrorConstant
end CurrentAFT.RationalMarkedSeedProgram.primaryErrorConstant
namespace CurrentAFT.RationalMarkedSeedProgram.seedDensity
end CurrentAFT.RationalMarkedSeedProgram.seedDensity
namespace CurrentAFT.RationalMarkedSeedProgram.uniformRelative
end CurrentAFT.RationalMarkedSeedProgram.uniformRelative
section
namespace CurrentAFT.RationalMarkedCertificateProgram
open AFT ControlCoordinates GradedControlAlgebra ActualControls MarkedPairCertificates
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalMarkedCertificateProgram.certificateFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h144 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalMarkedSeedProgram.inverseErrorConstant security := by
  simp only [_root_.CurrentAFT.RationalMarkedSeedProgram.inverseErrorConstant, _root_.CurrentAFT.RationalMarkedSeedProgram.seedErrorConstant, _root_.CurrentAFT.RationalMarkedSeedProgram.meanErrorConstant, _root_.CurrentAFT.RationalMarkedSeedProgram.profileBound, _root_.CurrentAFT.RationalMarkedSeedProgram.uniformErrorConstant, _root_.CurrentAFT.RationalMarkedSeedProgram.primaryErrorConstant, _root_.CurrentAFT.RationalBackgroundDensities.bodyErrorConstant, _root_.CurrentAFT.RationalBackgroundDensities.centerErrorConstant, _root_.CurrentAFT.RationalDensityInverseProgram.errorConstant, _root_.CurrentAFT.RationalDensityInverseProgram.inverseBound, _root_.CurrentAFT.RationalTensorInverseProgram.actualBound, _root_.CurrentAFT.RationalFirstResponseProgram.inverseErrorConstant]
  positivity
open _root_.P2Mb608f3c5 renaming h144 → _p2mH144
end
open _root_.P2Mb608f3c5 renaming h144 → _p2mH144
end CurrentAFT.RationalMarkedCertificateProgram
open _root_.P2Mb608f3c5 renaming h144 → _p2mH144
end
open _root_.P2Mb608f3c5 renaming h144 → _p2mH144
namespace CurrentAFT.RationalBackgroundDensities
end CurrentAFT.RationalBackgroundDensities
namespace CurrentAFT.RationalBackgroundDensities.body
end CurrentAFT.RationalBackgroundDensities.body
namespace CurrentAFT.RationalBackgroundDensities.centerErrorConstant
end CurrentAFT.RationalBackgroundDensities.centerErrorConstant
namespace CurrentAFT.RationalBackgroundDensities.primary
end CurrentAFT.RationalBackgroundDensities.primary
namespace CurrentAFT.RationalBackgroundDensities.residual
end CurrentAFT.RationalBackgroundDensities.residual
namespace CurrentAFT.RationalBackgroundTable
end CurrentAFT.RationalBackgroundTable
namespace CurrentAFT.RationalBackgroundTable.firstTable
end CurrentAFT.RationalBackgroundTable.firstTable
section
namespace CurrentAFT.RationalBackgroundProgram
open AFT ControlCoordinates GradedControlAlgebra BackgroundFamilies ActualControls
  RationalBackgroundTable RationalBackgroundDensities
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalBackgroundProgram.programFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h101 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalBackgroundDensities.primaryErrorConstant security ∧
    0 ≤ _root_.CurrentAFT.RationalBackgroundDensities.residualErrorConstant security ∧ 0 ≤ _root_.CurrentAFT.RationalBackgroundDensities.bodyErrorConstant security := by
  simp only [_root_.CurrentAFT.RationalBackgroundDensities.primaryErrorConstant, _root_.CurrentAFT.RationalBackgroundDensities.residualErrorConstant, _root_.CurrentAFT.RationalBackgroundDensities.bodyErrorConstant, _root_.CurrentAFT.RationalBackgroundDensities.centerErrorConstant,
    _root_.CurrentAFT.RationalMassLiftProgram.errorConstant, _root_.CurrentAFT.RationalTensorInverseProgram.actualBound,
    _root_.CurrentAFT.RationalDensityInverseProgram.inverseBound, _root_.CurrentAFT.RationalFirstResponseProgram.inverseErrorConstant]
  exact ⟨by positivity, by positivity, by positivity⟩
open _root_.P2Mb608f3c5 renaming h101 → _p2mH101
end
open _root_.P2Mb608f3c5 renaming h101 → _p2mH101
end CurrentAFT.RationalBackgroundProgram
open _root_.P2Mb608f3c5 renaming h101 → _p2mH101
end
open _root_.P2Mb608f3c5 renaming h101 → _p2mH101
namespace CurrentAFT.DiffusePairCertificates
end CurrentAFT.DiffusePairCertificates
namespace CurrentAFT.DiffusePairCertificates.diffuseCertificate
end CurrentAFT.DiffusePairCertificates.diffuseCertificate
namespace CurrentAFT.MarkedPairCertificates
end CurrentAFT.MarkedPairCertificates
namespace CurrentAFT.MarkedPairCertificates.mixedKernel
end CurrentAFT.MarkedPairCertificates.mixedKernel
namespace CurrentAFT.PairQuadraticFamilies
end CurrentAFT.PairQuadraticFamilies
namespace CurrentAFT.PrimaryDeviationCertificate.certificate
end CurrentAFT.PrimaryDeviationCertificate.certificate
namespace CurrentAFT.RationalActualFamilyApproximation
end CurrentAFT.RationalActualFamilyApproximation
namespace CurrentAFT.RationalBackgroundDensities.bodyErrorConstant
end CurrentAFT.RationalBackgroundDensities.bodyErrorConstant
namespace CurrentAFT.RationalBackgroundDensities.primaryErrorConstant
end CurrentAFT.RationalBackgroundDensities.primaryErrorConstant
namespace CurrentAFT.RationalBackgroundDensities.residualErrorConstant
end CurrentAFT.RationalBackgroundDensities.residualErrorConstant
namespace CurrentAFT.RationalBackgroundProgram
end CurrentAFT.RationalBackgroundProgram
namespace CurrentAFT.RationalDensityInverseProgram.errorConstant
end CurrentAFT.RationalDensityInverseProgram.errorConstant
namespace CurrentAFT.RationalDensityInverseProgram.inverseBound
end CurrentAFT.RationalDensityInverseProgram.inverseBound
namespace CurrentAFT.RationalFirstResponseProgram
end CurrentAFT.RationalFirstResponseProgram
namespace CurrentAFT.RationalFirstResponseProgram.inverseErrorConstant
end CurrentAFT.RationalFirstResponseProgram.inverseErrorConstant
namespace CurrentAFT.RationalMarkedCertificateProgram
end CurrentAFT.RationalMarkedCertificateProgram
namespace CurrentAFT.RationalMarkedCertificateProgram.ideal
end CurrentAFT.RationalMarkedCertificateProgram.ideal
namespace CurrentAFT.RationalMarkedSeedProgram.inverseErrorConstant
end CurrentAFT.RationalMarkedSeedProgram.inverseErrorConstant
namespace CurrentAFT.RationalMarkedSeedProgram.meanErrorConstant
end CurrentAFT.RationalMarkedSeedProgram.meanErrorConstant
namespace CurrentAFT.RationalMarkedSeedProgram.profileBound
end CurrentAFT.RationalMarkedSeedProgram.profileBound
namespace CurrentAFT.RationalMarkedSeedProgram.seedErrorConstant
end CurrentAFT.RationalMarkedSeedProgram.seedErrorConstant
namespace CurrentAFT.RationalMarkedSeedProgram.uniformErrorConstant
end CurrentAFT.RationalMarkedSeedProgram.uniformErrorConstant
namespace CurrentAFT.RationalMassLiftProgram
end CurrentAFT.RationalMassLiftProgram
namespace CurrentAFT.RationalMassLiftProgram.errorConstant
end CurrentAFT.RationalMassLiftProgram.errorConstant
namespace CurrentAFT.RationalPrimaryDeviationProgram
end CurrentAFT.RationalPrimaryDeviationProgram
namespace CurrentAFT.RationalPrimaryDeviationProgram.current
end CurrentAFT.RationalPrimaryDeviationProgram.current
namespace CurrentAFT.RationalPrimaryDeviationProgram.errorConstant
end CurrentAFT.RationalPrimaryDeviationProgram.errorConstant
namespace CurrentAFT.RationalPrimaryDeviationProgram.profile
end CurrentAFT.RationalPrimaryDeviationProgram.profile
namespace CurrentAFT.RationalPrimaryDeviationProgram.profileErrorConstant
end CurrentAFT.RationalPrimaryDeviationProgram.profileErrorConstant
namespace CurrentAFT.RationalTensorInverseProgram.actualBound
end CurrentAFT.RationalTensorInverseProgram.actualBound
section
namespace CurrentAFT.RationalMarkedPairProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus
  ProposalPrimary.primaryLaw ActualControls.bodyReference
  RationalPrimaryDeviationProgram.current RationalBackgroundProgram.free
  RationalMarkedCertificateProgram.current RationalFamilyProductProgram.product
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalMarkedPairProgram.markedPairFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h146 (security order : ℕ) (horder : 1 ≤ order) :
    ∀ arity colors centers,
      |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.BackgroundFamilies.freeCertificate security order horder) arity colors centers| ≤ _root_.CurrentAFT.RationalMarkedPairProgram.freeBound security order := by
  have hb : (1:ℝ) ≤ _root_.CurrentAFT.Parameters.base security := by
    exact_mod_cast (show 1 ≤ _root_.CurrentAFT.Parameters.base security by have := _root_.CurrentAFT.Parameters.base_ge_two security; omega)
  exact _p2mH88 security order _ 84 ((_root_.CurrentAFT.BackgroundFamilies.freeCertificate_norm_decay security order horder).trans
    (div_le_self (by norm_num) (one_le_pow₀ hb)))
open _root_.P2Mb608f3c5 renaming h146 → _p2mH146
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h145 (security order : ℕ) : 0 ≤ _root_.CurrentAFT.RationalMarkedPairProgram.errorConstant security order := by
  have hm := _p2mH144 security
  have hp := _p2mH170 security
  rcases _p2mH101 security with ⟨hfree, _, hbody⟩
  have hf : 0 ≤ _root_.CurrentAFT.RationalBackgroundProgram.freeErrorConstant security := by
    unfold _root_.CurrentAFT.RationalBackgroundProgram.freeErrorConstant
    positivity
  have hprod := _p2mH89 order (_root_.CurrentAFT.RationalMarkedPairProgram.primaryBound security order) (_root_.CurrentAFT.RationalMarkedPairProgram.freeBound security order)
    _ _ (by unfold _root_.CurrentAFT.RationalMarkedPairProgram.primaryBound _root_.CurrentAFT.RationalActualFamilyApproximation.coordinateFactor; positivity) (by unfold _root_.CurrentAFT.RationalMarkedPairProgram.freeBound _root_.CurrentAFT.RationalActualFamilyApproximation.coordinateFactor; positivity) hp hf
  exact add_nonneg hm hprod
open _root_.P2Mb608f3c5 renaming h145 → _p2mH145
end
open _root_.P2Mb608f3c5 renaming h145 → _p2mH145
open _root_.P2Mb608f3c5 renaming h146 → _p2mH146
end CurrentAFT.RationalMarkedPairProgram
open _root_.P2Mb608f3c5 renaming h145 → _p2mH145
open _root_.P2Mb608f3c5 renaming h146 → _p2mH146
end
open _root_.P2Mb608f3c5 renaming h145 → _p2mH145
open _root_.P2Mb608f3c5 renaming h146 → _p2mH146
namespace CurrentAFT.RationalMassLiftProgram.current
end CurrentAFT.RationalMassLiftProgram.current
section
namespace CurrentAFT.RationalMassLiftTensorProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalMassLiftTensorProgram.classicalFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw PublicParameterProgram.modulus
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h148 (security : ℕ) : 1 ≤ _root_.CurrentAFT.RationalMassLiftTensorProgram.factorBound security := by
  unfold _root_.CurrentAFT.RationalMassLiftTensorProgram.factorBound
  linarith [_p2mH191 security, _p2mH147 security]
open _root_.P2Mb608f3c5 renaming h148 → _p2mH148
end
open _root_.P2Mb608f3c5 renaming h148 → _p2mH148
end CurrentAFT.RationalMassLiftTensorProgram
open _root_.P2Mb608f3c5 renaming h148 → _p2mH148
end
open _root_.P2Mb608f3c5 renaming h148 → _p2mH148
namespace CurrentAFT.DiffusePairCertificates.residualMass
end CurrentAFT.DiffusePairCertificates.residualMass
namespace CurrentAFT.RationalDiffuseCertificateProgram
end CurrentAFT.RationalDiffuseCertificateProgram
namespace CurrentAFT.RationalDiffuseResidualProgram
end CurrentAFT.RationalDiffuseResidualProgram
namespace CurrentAFT.RationalDiffuseResidualProgram.bodyDensity
end CurrentAFT.RationalDiffuseResidualProgram.bodyDensity
namespace CurrentAFT.RationalMassLiftTensorProgram
end CurrentAFT.RationalMassLiftTensorProgram
namespace CurrentAFT.RationalMassLiftTensorProgram.entry
end CurrentAFT.RationalMassLiftTensorProgram.entry
section
namespace CurrentAFT.RationalDiffuseFamilyProgram
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram RationalDiffuseResidualProgram
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalDiffuseFamilyProgram.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff Parameters.safeMargin
  primaryLaw centerLaw PublicParameterProgram.modulus
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h103 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalDiffuseFamilyProgram.errorConstant security := by
  have hm := _p2mH147 security
  have hf := _p2mH148 security
  unfold _root_.CurrentAFT.RationalDiffuseFamilyProgram.errorConstant _root_.CurrentAFT.RationalDiffuseCertificateProgram.bodyErrorConstant _root_.CurrentAFT.RationalDiffuseFamilyProgram.primaryErrorConstant
    _root_.CurrentAFT.RationalMassLiftTensorProgram.errorConstant _root_.CurrentAFT.RationalDiffuseResidualProgram.pairBound _root_.CurrentAFT.RationalBackgroundDensities.centerErrorConstant
  positivity
open _root_.P2Mb608f3c5 renaming h103 → _p2mH103
end
open _root_.P2Mb608f3c5 renaming h103 → _p2mH103
end CurrentAFT.RationalDiffuseFamilyProgram
open _root_.P2Mb608f3c5 renaming h103 → _p2mH103
end
open _root_.P2Mb608f3c5 renaming h103 → _p2mH103
namespace CurrentAFT.MarkedPairCertificates.markedMixedCertificate
end CurrentAFT.MarkedPairCertificates.markedMixedCertificate
namespace CurrentAFT.RationalDiffuseFamilyProgram
end CurrentAFT.RationalDiffuseFamilyProgram
namespace CurrentAFT.RationalDiffuseFamilyProgram.bodyTable
end CurrentAFT.RationalDiffuseFamilyProgram.bodyTable
namespace CurrentAFT.RationalDiffuseFamilyProgram.primaryTable
end CurrentAFT.RationalDiffuseFamilyProgram.primaryTable
namespace CurrentAFT.RationalMarkedPairProgram
end CurrentAFT.RationalMarkedPairProgram
section
namespace CurrentAFT.RationalPairQuadraticProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies DiffuseProfiles
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw bodyReference
  RationalDiffuseFamilyProgram.current RationalMarkedPairProgram.current
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalPairQuadraticProgram.pairQuadraticFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h160 (security order : ℕ) : 0 ≤ _root_.CurrentAFT.RationalPairQuadraticProgram.errorConstant security order := by
  have hm := _p2mH145 security order
  have hd := _p2mH103 security
  unfold _root_.CurrentAFT.RationalPairQuadraticProgram.errorConstant _root_.CurrentAFT.RationalPairQuadraticProgram.diffuseBound _root_.CurrentAFT.RationalPairQuadraticProgram.markedBound _root_.CurrentAFT.RationalActualFamilyApproximation.coordinateFactor
  positivity
open _root_.P2Mb608f3c5 renaming h160 → _p2mH160
end
open _root_.P2Mb608f3c5 renaming h160 → _p2mH160
end CurrentAFT.RationalPairQuadraticProgram
open _root_.P2Mb608f3c5 renaming h160 → _p2mH160
end
open _root_.P2Mb608f3c5 renaming h160 → _p2mH160
namespace CurrentAFT.ConditionalPairLinear
end CurrentAFT.ConditionalPairLinear
namespace CurrentAFT.ConditionalPairLinear.certificate
end CurrentAFT.ConditionalPairLinear.certificate
namespace CurrentAFT.ConditionalPairLinear.wordMean
end CurrentAFT.ConditionalPairLinear.wordMean
namespace CurrentAFT.RationalFiniteMean
end CurrentAFT.RationalFiniteMean
section
namespace CurrentAFT.RationalConditionalPairProgram
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalConditionalPairProgram.conditionalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h102 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalConditionalPairProgram.errorConstant security := by
  simp only [_root_.CurrentAFT.RationalConditionalPairProgram.errorConstant, _root_.CurrentAFT.RationalConditionalPairProgram.computedBound, _root_.CurrentAFT.RationalConditionalPairProgram.profileErrorConstant, _root_.CurrentAFT.RationalMassLiftProgram.errorConstant,
    _root_.CurrentAFT.RationalTensorInverseProgram.actualBound, _root_.CurrentAFT.RationalDensityInverseProgram.inverseBound, _root_.CurrentAFT.RationalFirstResponseProgram.inverseErrorConstant]
  positivity
open _root_.P2Mb608f3c5 renaming h102 → _p2mH102
end
open _root_.P2Mb608f3c5 renaming h102 → _p2mH102
end CurrentAFT.RationalConditionalPairProgram
open _root_.P2Mb608f3c5 renaming h102 → _p2mH102
end
open _root_.P2Mb608f3c5 renaming h102 → _p2mH102
namespace CurrentAFT.BackgroundFamilies
end CurrentAFT.BackgroundFamilies
namespace CurrentAFT.BackgroundFamilies.translationCertificate
end CurrentAFT.BackgroundFamilies.translationCertificate
namespace CurrentAFT.BackgroundLinear
end CurrentAFT.BackgroundLinear
namespace CurrentAFT.BackgroundLinear.certificateNorm
end CurrentAFT.BackgroundLinear.certificateNorm
namespace CurrentAFT.BackgroundLinear.fixedQueueLinear
end CurrentAFT.BackgroundLinear.fixedQueueLinear
namespace CurrentAFT.BackgroundLinear.legLinearCertificate
end CurrentAFT.BackgroundLinear.legLinearCertificate
namespace CurrentAFT.BackgroundLinear.meanTranslation
end CurrentAFT.BackgroundLinear.meanTranslation
section
namespace CurrentAFT.RationalBackgroundLinearProgram
open AFT GaussianSource RationalNumerics GradedControlAlgebra ActualControls DiffuseProfiles ProposalPrimary BackgroundFamilies
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw centerLaw
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalBackgroundLinearProgram.linearFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h91 (security : ℕ) : _root_.CurrentAFT.RationalBackgroundLinearProgram.cutoff security = _root_.CurrentAFT.Parameters.sourceCutoff security-1 := by
  simp only [_root_.CurrentAFT.RationalBackgroundLinearProgram.cutoff, _root_.CurrentAFT.Parameters.sourceCutoff, _root_.CurrentAFT.Parameters.base]
open _root_.P2Mb608f3c5 renaming h91 → _p2mH91
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h92 (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.BackgroundFamilies.translationCertificate security order horder shift arity).val colors centers| ≤ _root_.CurrentAFT.RationalBackgroundLinearProgram.translationBound security order := by
  have hb : (1:ℝ) ≤ _root_.CurrentAFT.Parameters.base security := by exact_mod_cast (_root_.CurrentAFT.Parameters.base_ge_two security).trans' (by decide : 1≤2)
  have hn : _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order (_root_.CurrentAFT.BackgroundFamilies.translationCertificate security order horder shift) ≤ 56 := by
    apply (_root_.CurrentAFT.BackgroundFamilies.translationCertificate_norm_decay security order horder shift).trans
    exact div_le_self (by norm_num) (one_le_pow₀ hb)
  exact (_p2mH27 security order (_root_.CurrentAFT.BackgroundFamilies.translationCertificate security order horder shift) arity colors centers).trans
    ((mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (by unfold _root_.CurrentAFT.RationalBackgroundLinearProgram.translationBound; ring))
open _root_.P2Mb608f3c5 renaming h92 → _p2mH92
end
open _root_.P2Mb608f3c5 renaming h91 → _p2mH91
open _root_.P2Mb608f3c5 renaming h92 → _p2mH92
end CurrentAFT.RationalBackgroundLinearProgram
open _root_.P2Mb608f3c5 renaming h91 → _p2mH91
open _root_.P2Mb608f3c5 renaming h92 → _p2mH92
end
open _root_.P2Mb608f3c5 renaming h91 → _p2mH91
open _root_.P2Mb608f3c5 renaming h92 → _p2mH92
namespace CurrentAFT.RationalBackgroundLinearProgram
end CurrentAFT.RationalBackgroundLinearProgram
namespace CurrentAFT.RationalBackgroundLinearProgram.cutoff
end CurrentAFT.RationalBackgroundLinearProgram.cutoff
namespace CurrentAFT.RationalBackgroundLinearProgram.freeMass
end CurrentAFT.RationalBackgroundLinearProgram.freeMass
namespace CurrentAFT.RationalBackgroundLinearProgram.legLinear
end CurrentAFT.RationalBackgroundLinearProgram.legLinear
section
namespace CurrentAFT.RationalScalarFamilyAverage
open AFT GaussianSource RationalNumerics GradedControlAlgebra ActualControls DiffuseProfiles BackgroundFamilies
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalScalarFamilyAverage.scalarAverageFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h189 (security bits order : ℕ)
    (table : ℤ → _root_.CurrentAFT.RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → ℕ)
    (centers : Fin arity.val.2.val → ℕ) :
    _root_.CurrentAFT.RationalScalarFamilyAverage.current security bits order table arity colors centers =
      ∑ scalar : _root_.AFT.GaussianSource.Window (_root_.CurrentAFT.RationalBackgroundLinearProgram.cutoff security),
        _root_.CurrentAFT.RationalProposalProgram.gaussianWeight security (_root_.CurrentAFT.RationalBackgroundLinearProgram.cutoff security) bits scalar*
          table scalar.val arity colors centers := by
  unfold _root_.CurrentAFT.RationalScalarFamilyAverage.current
  exact (_root_.AFT.FiniteConvolutionProgram.windowIndexEquiv (_root_.CurrentAFT.RationalBackgroundLinearProgram.cutoff security)).sum_comp
    (fun scalar : _root_.AFT.GaussianSource.Window (_root_.CurrentAFT.RationalBackgroundLinearProgram.cutoff security) =>
      _root_.CurrentAFT.RationalProposalProgram.gaussianWeight security (_root_.CurrentAFT.RationalBackgroundLinearProgram.cutoff security) bits scalar*
        table scalar.val arity colors centers)
open _root_.P2Mb608f3c5 renaming h189 → _p2mH189
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h188 (security bits order : ℕ)
    (table : ℤ → _root_.CurrentAFT.RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (_root_.CurrentAFT.RationalScalarFamilyAverage.current security bits order table) arity colors centers =
      (_root_.AFT.RationalNumerics.windowApproxLaw (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security) (_root_.CurrentAFT.Parameters.sourceCutoff security-1) bits).expectation
        (fun scalar => _root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (table scalar.val) arity colors centers) := by
  change (_root_.CurrentAFT.RationalScalarFamilyAverage.current security bits order table arity (fun index => (colors index).val)
    (fun index => (centers index).val.val):ℝ) = _
  rw [_p2mH189]
  rw [Rat.cast_sum, _p2mH91]
  simp only [Rat.cast_mul, _root_.CurrentAFT.RationalProposalProgram.gaussianWeight_eq,
    _root_.AFT.FiniteDist.expectation, _root_.AFT.RationalNumerics.windowApproxLaw, _root_.CurrentAFT.RationalActualFamilyApproximation.interpret, _root_.CurrentAFT.RationalFamilyProductProgram.pullback,
    _root_.CurrentAFT.RationalFamilyProductProgram.realTable]
  rfl
open _root_.P2Mb608f3c5 renaming h188 → _p2mH188
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h187 (security order : ℕ)
    (families : _root_.CurrentAFT.MarkedPairSeed.Scalar security → _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RationalScalarFamilyAverage.actual security order families) arity colors centers =
      (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).expectation (fun scalar => _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (families scalar) arity colors centers) := by
  simp only [_root_.CurrentAFT.RationalScalarFamilyAverage.actual, _root_.CurrentAFT.RationalActualFamilyApproximation.data, _root_.AFT.FiniteDist.expectation, Finset.sum_apply, Submodule.coe_sum,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
open _root_.P2Mb608f3c5 renaming h187 → _p2mH187
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h190 (security bits order : ℕ)
    (families : _root_.CurrentAFT.MarkedPairSeed.Scalar security → _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order)
    (table : ℤ → _root_.CurrentAFT.RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (B e : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ scalar arity colors centers, |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (families scalar) arity colors centers| ≤ B)
    (herror : ∀ scalar arity colors centers,
      |_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (table scalar.val) arity colors centers-
        _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (families scalar) arity colors centers| ≤ e*(1/(2:ℝ)^bits))
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (_root_.CurrentAFT.RationalScalarFamilyAverage.current security bits order table) arity colors centers-
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RationalScalarFamilyAverage.actual security order families) arity colors centers| ≤ (e+B)*(1/(2:ℝ)^bits) := by
  let approximate := _root_.AFT.RationalNumerics.windowApproxLaw (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security) (_root_.CurrentAFT.Parameters.sourceCutoff security-1) bits
  let computed := fun scalar : _root_.CurrentAFT.MarkedPairSeed.Scalar security => _root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (table scalar.val) arity colors centers
  let ideal := fun scalar : _root_.CurrentAFT.MarkedPairSeed.Scalar security => _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (families scalar) arity colors centers
  have hpoint := _p2mH30 approximate
    (fun scalar => computed scalar-ideal scalar) (e*(1/(2:ℝ)^bits))
    (fun scalar => herror scalar arity colors centers)
  rw [_root_.AFT.FiniteDist.expectation_sub] at hpoint
  have hl1 := _p2mH13 (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security) (_root_.CurrentAFT.Parameters.sourceWidth security)
    (_root_.CurrentAFT.Parameters.sourceCutoff security-1) bits (_p2mH207 security)
    (_p2mH208 security).symm
  have hsource := (_p2mH42 approximate (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security) ideal B
    (fun scalar => hbound scalar arity colors centers)).trans (mul_le_mul_of_nonneg_left hl1 hB)
  rw [_p2mH188, _p2mH187]
  exact (abs_sub_le _ (approximate.expectation ideal) _).trans
    ((add_le_add hpoint hsource).trans_eq (by ring))
open _root_.P2Mb608f3c5 renaming h190 → CurrentAFT.RationalScalarFamilyAverage.current_error
open _root_.P2Mb608f3c5 renaming h190 → _p2mH190
end
open _root_.P2Mb608f3c5 renaming h187 → _p2mH187
open _root_.P2Mb608f3c5 renaming h188 → _p2mH188
open _root_.P2Mb608f3c5 renaming h189 → _p2mH189
open _root_.P2Mb608f3c5 renaming h190 → CurrentAFT.RationalScalarFamilyAverage.current_error
open _root_.P2Mb608f3c5 renaming h190 → _p2mH190
end CurrentAFT.RationalScalarFamilyAverage
open _root_.P2Mb608f3c5 renaming h187 → _p2mH187
open _root_.P2Mb608f3c5 renaming h188 → _p2mH188
open _root_.P2Mb608f3c5 renaming h189 → _p2mH189
open _root_.P2Mb608f3c5 renaming h190 → CurrentAFT.RationalScalarFamilyAverage.current_error
open _root_.P2Mb608f3c5 renaming h190 → _p2mH190
end
open _root_.P2Mb608f3c5 renaming h187 → _p2mH187
open _root_.P2Mb608f3c5 renaming h188 → _p2mH188
open _root_.P2Mb608f3c5 renaming h189 → _p2mH189
open _root_.P2Mb608f3c5 renaming h190 → CurrentAFT.RationalScalarFamilyAverage.current_error
open _root_.P2Mb608f3c5 renaming h190 → _p2mH190
namespace CurrentAFT.LegBackgroundFamilies
end CurrentAFT.LegBackgroundFamilies
namespace CurrentAFT.RationalActualFamilyApproximation.data
end CurrentAFT.RationalActualFamilyApproximation.data
namespace CurrentAFT.RationalConditionalPairProgram
end CurrentAFT.RationalConditionalPairProgram
namespace CurrentAFT.RationalConditionalPairProgram.centeredMean
end CurrentAFT.RationalConditionalPairProgram.centeredMean
namespace CurrentAFT.RationalConditionalPairProgram.colors
end CurrentAFT.RationalConditionalPairProgram.colors
namespace CurrentAFT.RationalConditionalPairProgram.computedBound
end CurrentAFT.RationalConditionalPairProgram.computedBound
namespace CurrentAFT.RationalConditionalPairProgram.current
end CurrentAFT.RationalConditionalPairProgram.current
namespace CurrentAFT.RationalConditionalPairProgram.errorConstant
end CurrentAFT.RationalConditionalPairProgram.errorConstant
namespace CurrentAFT.RationalConditionalPairProgram.profileErrorConstant
end CurrentAFT.RationalConditionalPairProgram.profileErrorConstant
namespace CurrentAFT.RationalPairQuadraticProgram
end CurrentAFT.RationalPairQuadraticProgram
namespace CurrentAFT.RationalPairQuadraticProgram.current
end CurrentAFT.RationalPairQuadraticProgram.current
namespace CurrentAFT.RationalScalarFamilyAverage
end CurrentAFT.RationalScalarFamilyAverage
namespace CurrentAFT.RationalScalarFamilyAverage.actual
end CurrentAFT.RationalScalarFamilyAverage.actual
section
namespace CurrentAFT.RationalLegBackgroundProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies DiffuseProfiles
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw bodyReference
  RationalPairQuadraticProgram.current RationalConditionalPairProgram.current
  RationalBackgroundProgram.translation RationalFamilyProductProgram.product
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalLegBackgroundProgram.legBackgroundFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h143 (security : ℕ) : 0 ≤ _root_.CurrentAFT.RationalBackgroundProgram.translationErrorConstant security := by
  rcases _p2mH101 security with ⟨hp, hr, hb⟩
  unfold _root_.CurrentAFT.RationalBackgroundProgram.translationErrorConstant
  positivity
open _root_.P2Mb608f3c5 renaming h143 → _p2mH143
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h142 (security order : ℕ) : 0 ≤ _root_.CurrentAFT.RationalLegBackgroundProgram.errorConstant security order := by
  have hp := _p2mH102 security
  have hpair := _p2mH160 security order
  have ht := _p2mH143 security
  rcases _p2mH101 security with ⟨hprimary, _, hbody⟩
  have hf : 0 ≤ _root_.CurrentAFT.RationalBackgroundProgram.freeErrorConstant security := by
    unfold _root_.CurrentAFT.RationalBackgroundProgram.freeErrorConstant
    positivity
  have hm : 0 ≤ _root_.CurrentAFT.RationalBackgroundLinearProgram.meanErrorConstant security order := by
    unfold _root_.CurrentAFT.RationalBackgroundLinearProgram.meanErrorConstant _root_.CurrentAFT.RationalBackgroundLinearProgram.translationBound
    positivity
  have hl : 0 ≤ _root_.CurrentAFT.RationalBackgroundLinearProgram.linearErrorConstant security order := by
    unfold _root_.CurrentAFT.RationalBackgroundLinearProgram.linearErrorConstant
    exact div_nonneg (add_nonneg (mul_nonneg (_root_.CurrentAFT.ProposalPrimary.freeMass_nonneg security) hf)
      (mul_nonneg (Nat.cast_nonneg _) hm)) (Nat.cast_nonneg _)
  have hprod1 := _p2mH89 order (_root_.CurrentAFT.RationalLegBackgroundProgram.conditionalLinearBound security order)
    (_root_.CurrentAFT.RationalBackgroundLinearProgram.translationBound security order) _ _
    (by unfold _root_.CurrentAFT.RationalLegBackgroundProgram.conditionalLinearBound _root_.CurrentAFT.RationalActualFamilyApproximation.coordinateFactor; positivity)
    (by unfold _root_.CurrentAFT.RationalBackgroundLinearProgram.translationBound; positivity) hp ht
  have hprod2 := _p2mH89 order (_root_.CurrentAFT.RationalLegBackgroundProgram.pairBound security order)
    (_root_.CurrentAFT.RationalBackgroundLinearProgram.translationBound security order) _ _
    (by unfold _root_.CurrentAFT.RationalLegBackgroundProgram.pairBound _root_.CurrentAFT.RationalActualFamilyApproximation.coordinateFactor; positivity)
    (by unfold _root_.CurrentAFT.RationalBackgroundLinearProgram.translationBound; positivity) hpair ht
  unfold _root_.CurrentAFT.RationalLegBackgroundProgram.errorConstant _root_.CurrentAFT.RationalLegBackgroundProgram.conditionalQuadraticError _root_.CurrentAFT.RationalLegBackgroundProgram.conditionalCubicError _root_.CurrentAFT.RationalLegBackgroundProgram.quadraticBound _root_.CurrentAFT.RationalLegBackgroundProgram.cubicBound _root_.CurrentAFT.RationalActualFamilyApproximation.coordinateFactor
  positivity
open _root_.P2Mb608f3c5 renaming h142 → _p2mH142
end
open _root_.P2Mb608f3c5 renaming h142 → _p2mH142
open _root_.P2Mb608f3c5 renaming h143 → _p2mH143
end CurrentAFT.RationalLegBackgroundProgram
open _root_.P2Mb608f3c5 renaming h142 → _p2mH142
open _root_.P2Mb608f3c5 renaming h143 → _p2mH143
end
open _root_.P2Mb608f3c5 renaming h142 → _p2mH142
open _root_.P2Mb608f3c5 renaming h143 → _p2mH143
section
namespace CurrentAFT.RationalPopulationApproximation
open AFT GradedControlAlgebra ActualControls BackgroundFamilies
open RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h163 (security order population : ℕ) (family : _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order)
    (hzero : family (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order)=0) :
    _root_.CurrentAFT.RationalFamilyProductProgram.binomial order population (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order family) =
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order ((1+family)^population) :=
  _p2mH107 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
    order population family hzero
open _root_.P2Mb608f3c5 renaming h163 → _p2mH163
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h162 (order population : ℕ) (A : ℝ) (hA : 0 ≤ A) : 0 ≤ _root_.CurrentAFT.RationalPopulationApproximation.bound order population A := by
  have hg := (_p2mH109 order A 0 hA (by norm_num)).trans' (by norm_num : (0:ℝ)≤1)
  unfold _root_.CurrentAFT.RationalPopulationApproximation.bound
  positivity
open _root_.P2Mb608f3c5 renaming h162 → _p2mH162
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h164 (order population : ℕ) (A e : ℝ) (hA : 0 ≤ A) (he : 0 ≤ e) :
    0 ≤ _root_.CurrentAFT.RationalPopulationApproximation.error order population A e := by
  have hg := (_p2mH109 order A e hA he).trans' (by norm_num : (0:ℝ)≤1)
  unfold _root_.CurrentAFT.RationalPopulationApproximation.error
  positivity
open _root_.P2Mb608f3c5 renaming h164 → _p2mH164
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h161 (security order population : ℕ) (family : _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order)
    (hzero : family (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order)=0) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ arity colors centers, |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order family arity colors centers| ≤ A)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order ((1+family)^population) arity colors centers| ≤ _root_.CurrentAFT.RationalPopulationApproximation.bound order population A := by
  rw [← _p2mH163 security order population family hzero]
  let scale := _root_.CurrentAFT.RationalFamilyProductProgram.growth order A 0
  have hs : 1 ≤ scale := _p2mH109 order A 0 hA (by norm_num)
  have hscale : (Nat.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order):ℝ)^2*A ≤ scale := by
    unfold scale _root_.CurrentAFT.RationalFamilyProductProgram.growth
    nlinarith [sq_nonneg (Nat.card (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order):ℝ)]
  unfold _root_.CurrentAFT.RationalFamilyProductProgram.binomial
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _count ∈ Finset.range (order+1), ((population+1:ℕ):ℝ)^(order+1)*scale^(order+1) := by
      apply Finset.sum_le_sum
      intro count hcount
      have hc : count ≤ order+1 := by have := Finset.mem_range.mp hcount; omega
      have hn : (population.choose count:ℝ) ≤ ((population+1:ℕ):ℝ)^(order+1) := by
        exact_mod_cast (Nat.choose_le_pow population count).trans
          ((Nat.pow_le_pow_left (by omega : population≤population+1) count).trans (Nat.pow_le_pow_right (by omega : 1≤population+1) hc))
      have hp := (_p2mH116 order (_root_.CurrentAFT.RationalActualFamilyApproximation.data security order family) A scale hA hs hscale ha count arity colors centers).trans
        (pow_le_pow_right₀ hs hc)
      rw [abs_mul, abs_of_nonneg (show (0:ℝ)≤population.choose count by positivity)]
      exact mul_le_mul hn hp (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.CurrentAFT.RationalPopulationApproximation.bound]; dsimp only [scale]; ring
open _root_.P2Mb608f3c5 renaming h161 → _p2mH161
end
open _root_.P2Mb608f3c5 renaming h161 → _p2mH161
open _root_.P2Mb608f3c5 renaming h162 → _p2mH162
open _root_.P2Mb608f3c5 renaming h163 → _p2mH163
open _root_.P2Mb608f3c5 renaming h164 → _p2mH164
end CurrentAFT.RationalPopulationApproximation
open _root_.P2Mb608f3c5 renaming h161 → _p2mH161
open _root_.P2Mb608f3c5 renaming h162 → _p2mH162
open _root_.P2Mb608f3c5 renaming h163 → _p2mH163
open _root_.P2Mb608f3c5 renaming h164 → _p2mH164
end
open _root_.P2Mb608f3c5 renaming h161 → _p2mH161
open _root_.P2Mb608f3c5 renaming h162 → _p2mH162
open _root_.P2Mb608f3c5 renaming h163 → _p2mH163
open _root_.P2Mb608f3c5 renaming h164 → _p2mH164
namespace CurrentAFT.ActualBackground
end CurrentAFT.ActualBackground
namespace CurrentAFT.ActualBackground.background
end CurrentAFT.ActualBackground.background
namespace CurrentAFT.ActualBackground.fixedQueueBackground
end CurrentAFT.ActualBackground.fixedQueueBackground
namespace CurrentAFT.ActualBackground.numericalThreshold
end CurrentAFT.ActualBackground.numericalThreshold
namespace CurrentAFT.RationalLegBackgroundProgram
end CurrentAFT.RationalLegBackgroundProgram
namespace CurrentAFT.RationalLegBackgroundProgram.base_one
end CurrentAFT.RationalLegBackgroundProgram.base_one
namespace CurrentAFT.RationalLegBackgroundProgram.current
end CurrentAFT.RationalLegBackgroundProgram.current
namespace CurrentAFT.RationalPopulationApproximation
end CurrentAFT.RationalPopulationApproximation
namespace CurrentAFT.RationalPopulationApproximation.bound
end CurrentAFT.RationalPopulationApproximation.bound
section
namespace CurrentAFT.RationalBackgroundPopulationProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies BackgroundScalarZero
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  PublicParameterProgram.modulus ProposalPrimary.primaryLaw bodyReference
  RationalBackgroundProgram.free RationalBackgroundProgram.translation RationalLegBackgroundProgram.current
  RationalFamilyProductProgram.binomial RationalFamilyProductProgram.product
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalBackgroundPopulationProgram.populationFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h98 (security order : ℕ) (horder : 2≤order) :
    ∀ arity colors centers, |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.LegBackgroundFamilies.completeLegAtom security order horder) arity colors centers| ≤ _root_.CurrentAFT.RationalBackgroundPopulationProgram.legAtomBound security order := by
  have hb : (1:ℝ)≤_root_.CurrentAFT.Parameters.base security := by
    exact_mod_cast (show 1≤_root_.CurrentAFT.Parameters.base security by have := _root_.CurrentAFT.Parameters.base_ge_two security; omega)
  exact _p2mH88 security order _ 43377248 ((_root_.CurrentAFT.LegBackgroundFamilies.completeLegAtom_norm security order horder).trans
    (div_le_self (by norm_num) (one_le_pow₀ hb)))
open _root_.P2Mb608f3c5 renaming h98 → _p2mH98
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h95 (security order : ℕ) :
    0≤_root_.CurrentAFT.RationalBackgroundPopulationProgram.freeBound security order ∧ 0≤_root_.CurrentAFT.RationalBackgroundPopulationProgram.queueBound security order ∧ 0≤_root_.CurrentAFT.RationalBackgroundPopulationProgram.legBound security order ∧
    0≤_root_.CurrentAFT.RationalBackgroundPopulationProgram.freeError security order ∧ 0≤_root_.CurrentAFT.RationalBackgroundPopulationProgram.queueError security order ∧ 0≤_root_.CurrentAFT.RationalBackgroundPopulationProgram.legError security order := by
  have hfA : 0≤_root_.CurrentAFT.RationalMarkedPairProgram.freeBound security order := by
    unfold _root_.CurrentAFT.RationalMarkedPairProgram.freeBound _root_.CurrentAFT.RationalActualFamilyApproximation.coordinateFactor; positivity
  have hqA : 0≤_root_.CurrentAFT.RationalBackgroundLinearProgram.translationBound security order := by
    unfold _root_.CurrentAFT.RationalBackgroundLinearProgram.translationBound; positivity
  have hlA : 0≤_root_.CurrentAFT.RationalBackgroundPopulationProgram.legAtomBound security order := by unfold _root_.CurrentAFT.RationalBackgroundPopulationProgram.legAtomBound _root_.CurrentAFT.RationalActualFamilyApproximation.coordinateFactor; positivity
  rcases _p2mH101 security with ⟨hp, _, hb⟩
  have hfE : 0≤_root_.CurrentAFT.RationalBackgroundProgram.freeErrorConstant security := by
    unfold _root_.CurrentAFT.RationalBackgroundProgram.freeErrorConstant; positivity
  exact ⟨_p2mH162 _ _ _ hfA,
    _p2mH162 _ _ _ hqA,
    _p2mH162 _ _ _ hlA,
    _p2mH164 _ _ _ _ hfA hfE,
    _p2mH164 _ _ _ _ hqA (_p2mH143 security),
    _p2mH164 _ _ _ _ hlA (_p2mH142 security order)⟩
open _root_.P2Mb608f3c5 renaming h95 → _p2mH95
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h97 (security order : ℕ) (horder : 2≤order) :
    ∀ arity colors centers, |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RationalBackgroundPopulationProgram.freeActual security order horder) arity colors centers| ≤ _root_.CurrentAFT.RationalBackgroundPopulationProgram.freeBound security order :=
  _p2mH161 security order _ _ (_root_.CurrentAFT.BackgroundScalarZero.freeCertificate_zero security order (by omega))
    _ (by unfold _root_.CurrentAFT.RationalMarkedPairProgram.freeBound _root_.CurrentAFT.RationalActualFamilyApproximation.coordinateFactor; positivity) (_p2mH146 security order (by omega))
open _root_.P2Mb608f3c5 renaming h97 → _p2mH97
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h100 (security order : ℕ) (horder : 2≤order) (queue : ℤ) :
    ∀ arity colors centers, |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RationalBackgroundPopulationProgram.queueActual security order horder queue) arity colors centers| ≤ _root_.CurrentAFT.RationalBackgroundPopulationProgram.queueBound security order :=
  _p2mH161 security order _ _ (_root_.CurrentAFT.BackgroundScalarZero.translationCertificate_zero security order (by omega) queue)
    _ (by unfold _root_.CurrentAFT.RationalBackgroundLinearProgram.translationBound; positivity) (_p2mH92 security order (by omega) queue)
open _root_.P2Mb608f3c5 renaming h100 → _p2mH100
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h99 (security order : ℕ) (horder : 2≤order) :
    ∀ arity colors centers, |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.RationalBackgroundPopulationProgram.legActual security order horder) arity colors centers| ≤ _root_.CurrentAFT.RationalBackgroundPopulationProgram.legBound security order :=
  _p2mH161 security order _ _ (_root_.CurrentAFT.BackgroundScalarZero.completeLegAtom_zero security order horder)
    _ (by unfold _root_.CurrentAFT.RationalBackgroundPopulationProgram.legAtomBound _root_.CurrentAFT.RationalActualFamilyApproximation.coordinateFactor; positivity) (_p2mH98 security order horder)
open _root_.P2Mb608f3c5 renaming h99 → _p2mH99
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h96 (security order : ℕ) : 0≤_root_.CurrentAFT.RationalBackgroundPopulationProgram.errorConstant security order := by
  rcases _p2mH95 security order with ⟨hf, hq, hl, heF, heQ, heL⟩
  exact _p2mH89 _ _ _ _ _ (by unfold _root_.CurrentAFT.RationalBackgroundPopulationProgram.freeQueueBound; positivity) hl
    (_p2mH89 _ _ _ _ _ hf hq heF heQ) heL
open _root_.P2Mb608f3c5 renaming h96 → _p2mH96
end
open _root_.P2Mb608f3c5 renaming h95 → _p2mH95
open _root_.P2Mb608f3c5 renaming h96 → _p2mH96
open _root_.P2Mb608f3c5 renaming h97 → _p2mH97
open _root_.P2Mb608f3c5 renaming h98 → _p2mH98
open _root_.P2Mb608f3c5 renaming h99 → _p2mH99
open _root_.P2Mb608f3c5 renaming h100 → _p2mH100
end CurrentAFT.RationalBackgroundPopulationProgram
open _root_.P2Mb608f3c5 renaming h95 → _p2mH95
open _root_.P2Mb608f3c5 renaming h96 → _p2mH96
open _root_.P2Mb608f3c5 renaming h97 → _p2mH97
open _root_.P2Mb608f3c5 renaming h98 → _p2mH98
open _root_.P2Mb608f3c5 renaming h99 → _p2mH99
open _root_.P2Mb608f3c5 renaming h100 → _p2mH100
end
open _root_.P2Mb608f3c5 renaming h95 → _p2mH95
open _root_.P2Mb608f3c5 renaming h96 → _p2mH96
open _root_.P2Mb608f3c5 renaming h97 → _p2mH97
open _root_.P2Mb608f3c5 renaming h98 → _p2mH98
open _root_.P2Mb608f3c5 renaming h99 → _p2mH99
open _root_.P2Mb608f3c5 renaming h100 → _p2mH100
namespace CurrentAFT.BackgroundPopulationBounds
end CurrentAFT.BackgroundPopulationBounds
namespace CurrentAFT.BackgroundPopulationBounds.freeCount
end CurrentAFT.BackgroundPopulationBounds.freeCount
namespace CurrentAFT.CurrentGroupSourcePadding.groupKind.match_1
end CurrentAFT.CurrentGroupSourcePadding.groupKind.match_1
namespace CurrentAFT.GroupSourcePadding.indexEquiv
end CurrentAFT.GroupSourcePadding.indexEquiv
namespace CurrentAFT.GroupSourcePadding.sourceDecode
end CurrentAFT.GroupSourcePadding.sourceDecode
namespace CurrentAFT.RationalBackgroundPopulationProgram
end CurrentAFT.RationalBackgroundPopulationProgram
namespace CurrentAFT.RationalBackgroundPopulationProgram.freeCount
end CurrentAFT.RationalBackgroundPopulationProgram.freeCount
namespace CurrentAFT.RationalPackedRootProgram
end CurrentAFT.RationalPackedRootProgram
namespace CurrentAFT.RationalPackedRootProgram.actualMetadata
end CurrentAFT.RationalPackedRootProgram.actualMetadata
namespace CurrentAFT.RationalPackedRootProgram.nativeKind
end CurrentAFT.RationalPackedRootProgram.nativeKind
namespace CurrentAFT.RationalPackedRootProgram.nativeKind.match_1
end CurrentAFT.RationalPackedRootProgram.nativeKind.match_1
namespace CurrentAFT.RationalPackedRootProgram.nativeRole
end CurrentAFT.RationalPackedRootProgram.nativeRole
namespace CurrentAFT.RationalPackedRootProgram.nativeRole.match_3
end CurrentAFT.RationalPackedRootProgram.nativeRole.match_3
namespace CurrentAFT.RationalPackedRootProgram.sourceIndex
end CurrentAFT.RationalPackedRootProgram.sourceIndex
section
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock TaggedSelection GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h139 (security r s : ℕ) (choice : _root_.CurrentAFT.UniformTaggedOutput.Choice security r s) :
    _root_.CurrentAFT.RationalFullResponseProgram.selection security r s choice = _root_.CurrentAFT.UniformTaggedOutput.selection security r s choice := rfl
open _root_.P2Mb608f3c5 renaming h139 → _p2mH139
end CurrentAFT.RationalFullResponseProgram
open _root_.P2Mb608f3c5 renaming h139 → _p2mH139
end
open _root_.P2Mb608f3c5 renaming h139 → _p2mH139
namespace CurrentAFT.EmptyRootCoefficientIdentity
end CurrentAFT.EmptyRootCoefficientIdentity
namespace CurrentAFT.RationalFullResponseProgram
end CurrentAFT.RationalFullResponseProgram
section
namespace CurrentAFT.FullResponseWeightedIdentity
open AFT ActualBlockFock TaggedSelection GradedControlAlgebra LocalCoefficientFamily
  ActualControls ProposalPrimary ControlCoordinates ControlProduct CanonicalReconstruction
  UniformTaggedOutput ActualRootFamily FullResponsePointFormula ActualBackground
  RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.FullResponseWeightedIdentity.finDecidableEq
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  primaryLaw bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h63 (security order : ℕ) (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) :
    (Pi.single source.1 (_root_.CurrentAFT.FullResponseWeightedIdentity.sourceKernel security order source) : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) =
      _root_.CurrentAFT.FullResponsePointFormula.referenceWeight security order source • _root_.CurrentAFT.FullResponsePointFormula.basisFamily security order source := by
  funext output
  by_cases he : output=source.1
  · subst output
    simp only [_root_.CurrentAFT.FullResponsePointFormula.basisFamily, Pi.smul_apply, Pi.single_eq_same, _root_.CurrentAFT.FullResponseWeightedIdentity.sourceKernel,
      _root_.CurrentAFT.WeightedPointKernelProgram.actualKernel, _root_.CurrentAFT.FullResponsePointFormula.referenceWeight]
  · simp only [_root_.CurrentAFT.FullResponsePointFormula.basisFamily, Pi.smul_apply, Pi.single_eq_of_ne he, smul_zero]
open _root_.P2Mb608f3c5 renaming h63 → _p2mH63
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h62 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) (chosen : _root_.CurrentAFT.TaggedSelection.Selection security source.1.val.1.val source.1.val.2.val)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    _root_.CurrentAFT.FullResponseWeightedIdentity.selected security order horder queue source chosen layout =
      _root_.CurrentAFT.FullResponsePointFormula.referenceWeight security order source •
        (_root_.CurrentAFT.FullResponsePointFormula.basisFamily security order source+_root_.CurrentAFT.CompleteRaising.raisingLinear security order horder (_root_.CurrentAFT.FullResponsePointFormula.basisFamily security order source))+
      _root_.CurrentAFT.FullResponsePointFormula.referenceWeight security order source •
        (∑ tagged ∈ _root_.CurrentAFT.RationalFullResponseProgram.tags security order,
          _root_.CurrentAFT.ActualRootResponse.response order horder queue chosen tagged layout
            (_root_.CurrentAFT.CanonicalReconstruction.pointKernel (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.ActualControls.primaryReference_positive security)
              (_root_.CurrentAFT.ActualControls.bodyReference_positive security) source.2.1 source.2.2)) := by
  unfold _root_.CurrentAFT.FullResponseWeightedIdentity.selected
  rw [_p2mH48 security order horder queue source.1,
    _p2mH63, map_smul, ← smul_add]
  congr 1
  simp only [_root_.CurrentAFT.FullResponseWeightedIdentity.sourceKernel, _root_.CurrentAFT.WeightedPointKernelProgram.actualKernel, _root_.CurrentAFT.FullResponsePointFormula.referenceWeight, map_smul, Finset.smul_sum]
open _root_.P2Mb608f3c5 renaming h62 → _p2mH62
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h59 (security order : ℕ) (horder : 1 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    _root_.CurrentAFT.FullResponseWeightedIdentity.choiceAverage security order horder hroom queue source layout =
      _root_.CurrentAFT.FullResponsePointFormula.referenceWeight security order source •
        (_root_.CurrentAFT.FullResponsePointFormula.basisFamily security order source+_root_.CurrentAFT.CompleteRaising.raisingLinear security order horder (_root_.CurrentAFT.FullResponsePointFormula.basisFamily security order source)+
          _root_.CurrentAFT.FullResponsePointFormula.rootPointResponse security order horder hroom queue layout source) := by
  simp only [_root_.CurrentAFT.FullResponseWeightedIdentity.choiceAverage, _p2mH62, smul_add, Finset.sum_add_distrib,
    ← Finset.sum_smul, _root_.AFT.FiniteDist.sum_one, one_smul]
  congr 1
  unfold _root_.CurrentAFT.FullResponsePointFormula.rootPointResponse
  simp only [Finset.smul_sum, _root_.CurrentAFT.RationalFullResponseProgram.tags, smul_smul]
  apply Finset.sum_congr rfl
  intro choice _
  rw [mul_comm]
  apply Finset.sum_congr (by ext tagged; simp only [Finset.mem_filter, _p2mH51])
  intro tagged _
  rfl
open _root_.P2Mb608f3c5 renaming h59 → _p2mH59
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h61 (security order : ℕ) (horder : 2 ≤ order) (hroom : 2*order ≤ security)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    _root_.CurrentAFT.FullResponseWeightedIdentity.response security order horder hroom source layout =
      _root_.CurrentAFT.FullResponsePointFormula.referenceWeight security order source • _root_.CurrentAFT.FullResponsePointFormula.pointResponse security order horder hroom layout source := by
  let baseline := _root_.CurrentAFT.FullResponsePointFormula.basisFamily security order source+
    _root_.CurrentAFT.CompleteRaising.raisingLinear security order (by omega) (_root_.CurrentAFT.FullResponsePointFormula.basisFamily security order source)
  have hterm (scalar : _root_.CurrentAFT.FirstHistogram.Scalar security) :
      (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar •
        (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder scalar.val *
          (_root_.CurrentAFT.FullResponsePointFormula.referenceWeight security order source •
            (baseline+_root_.CurrentAFT.FullResponsePointFormula.rootPointResponse security order (by omega) hroom scalar.val layout source))) =
      _root_.CurrentAFT.FullResponsePointFormula.referenceWeight security order source •
        ((_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar • (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder scalar.val*baseline)+
          (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar • (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder scalar.val*
            _root_.CurrentAFT.FullResponsePointFormula.rootPointResponse security order (by omega) hroom scalar.val layout source)) := by
    rw [mul_smul_comm, smul_comm, mul_add, smul_add]
  unfold _root_.CurrentAFT.FullResponseWeightedIdentity.response _root_.CurrentAFT.FullResponseWeightedIdentity.fixedQueue
  simp_rw [_p2mH59]
  change (∑ scalar, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar •
    (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder scalar.val *
      (_root_.CurrentAFT.FullResponsePointFormula.referenceWeight security order source •
        (baseline+_root_.CurrentAFT.FullResponsePointFormula.rootPointResponse security order (by omega) hroom scalar.val layout source)))) = _
  simp_rw [hterm]
  rw [← Finset.smul_sum, Finset.sum_add_distrib]
  congr 1
  unfold _root_.CurrentAFT.FullResponsePointFormula.pointResponse
  congr 1
  simp only [← smul_mul_assoc, ← Finset.sum_mul]
  rfl
open _root_.P2Mb608f3c5 renaming h61 → CurrentAFT.FullResponseWeightedIdentity.response_eq
open _root_.P2Mb608f3c5 renaming h61 → _p2mH61
end
open _root_.P2Mb608f3c5 renaming h59 → _p2mH59
open _root_.P2Mb608f3c5 renaming h61 → CurrentAFT.FullResponseWeightedIdentity.response_eq
open _root_.P2Mb608f3c5 renaming h61 → _p2mH61
open _root_.P2Mb608f3c5 renaming h62 → _p2mH62
open _root_.P2Mb608f3c5 renaming h63 → _p2mH63
end CurrentAFT.FullResponseWeightedIdentity
open _root_.P2Mb608f3c5 renaming h59 → _p2mH59
open _root_.P2Mb608f3c5 renaming h61 → CurrentAFT.FullResponseWeightedIdentity.response_eq
open _root_.P2Mb608f3c5 renaming h61 → _p2mH61
open _root_.P2Mb608f3c5 renaming h62 → _p2mH62
open _root_.P2Mb608f3c5 renaming h63 → _p2mH63
end
open _root_.P2Mb608f3c5 renaming h59 → _p2mH59
open _root_.P2Mb608f3c5 renaming h61 → CurrentAFT.FullResponseWeightedIdentity.response_eq
open _root_.P2Mb608f3c5 renaming h61 → _p2mH61
open _root_.P2Mb608f3c5 renaming h62 → _p2mH62
open _root_.P2Mb608f3c5 renaming h63 → _p2mH63
namespace CurrentAFT.CalibrationTableNorm
end CurrentAFT.CalibrationTableNorm
namespace CurrentAFT.CalibrationTableNorm.decodeCurrent
end CurrentAFT.CalibrationTableNorm.decodeCurrent
namespace CurrentAFT.CalibrationTableNorm.decodeFactor
end CurrentAFT.CalibrationTableNorm.decodeFactor
namespace CurrentAFT.CalibrationTableNorm.encodeCurrent
end CurrentAFT.CalibrationTableNorm.encodeCurrent
namespace CurrentAFT.CalibrationTableNorm.exactDefect
end CurrentAFT.CalibrationTableNorm.exactDefect
namespace CurrentAFT.CalibrationTableNorm.measure
end CurrentAFT.CalibrationTableNorm.measure
namespace CurrentAFT.CalibrationTableNorm.remainder
end CurrentAFT.CalibrationTableNorm.remainder
namespace CurrentAFT.FullResponseWeightedIdentity
end CurrentAFT.FullResponseWeightedIdentity
namespace CurrentAFT.FullResponseWeightedIdentity.choiceAverage
end CurrentAFT.FullResponseWeightedIdentity.choiceAverage
namespace CurrentAFT.FullResponseWeightedIdentity.selected
end CurrentAFT.FullResponseWeightedIdentity.selected
namespace CurrentAFT.FullResponseWeightedIdentity.sourceKernel
end CurrentAFT.FullResponseWeightedIdentity.sourceKernel
namespace CurrentAFT.RationalFullResponseProgram.tags
end CurrentAFT.RationalFullResponseProgram.tags
namespace CurrentAFT.WeightedPointKernelProgram
end CurrentAFT.WeightedPointKernelProgram
namespace CurrentAFT.WeightedPointKernelProgram.actualKernel
end CurrentAFT.WeightedPointKernelProgram.actualKernel
section
namespace CurrentAFT.FullResponseWeightedIdentity
open AFT ActualBlockFock GradedControlAlgebra LocalCoefficientFamily
  ActualControls ProposalPrimary FullResponsePointFormula RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.FullResponseWeightedIdentity.defectFinDecidableEq
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension primaryLaw bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h60 (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) (output source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) :
    LinearMap.toMatrix' (_root_.CurrentAFT.CalibrationTableNorm.exactDefect security order horder hsecurity layout) output source =
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.FullResponseWeightedIdentity.response security order horder (_root_.CurrentAFT.ActualCompleteStability.room security order horder hsecurity) source layout)
        output.1 output.2.1 output.2.2-
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (Pi.single source.1 (_root_.CurrentAFT.FullResponseWeightedIdentity.sourceKernel security order source)) output.1 output.2.1 output.2.2 := by
  rw [_p2mH31]
  simp only [Matrix.sub_apply, _p2mH54,
    _p2mH61, _p2mH63, _root_.CurrentAFT.RationalActualFamilyApproximation.data, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul]
  by_cases he : output=source
  · subst output
    simp only [ite_true, Matrix.one_apply_eq]
    ring
  · simp only [if_neg he, Matrix.one_apply_ne he]
    ring
open _root_.P2Mb608f3c5 renaming h60 → _p2mH60
end
open _root_.P2Mb608f3c5 renaming h60 → _p2mH60
end CurrentAFT.FullResponseWeightedIdentity
open _root_.P2Mb608f3c5 renaming h60 → _p2mH60
end
open _root_.P2Mb608f3c5 renaming h60 → _p2mH60
namespace CurrentAFT.RationalPairedLiftProgram
end CurrentAFT.RationalPairedLiftProgram
namespace CurrentAFT.RationalPairedLiftProgram.anchorProfile
end CurrentAFT.RationalPairedLiftProgram.anchorProfile
namespace CurrentAFT.RationalPairedLiftProgram.current
end CurrentAFT.RationalPairedLiftProgram.current
namespace CurrentAFT.inversePower
end CurrentAFT.inversePower
section
namespace CurrentAFT.NumericReferenceBudgets
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h66 (degree : ℕ) :
    Tendsto (fun security : ℕ => (_root_.CurrentAFT.Parameters.base security:ℝ)^degree/(2:ℝ)^security) atTop (𝓝 0) := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt degree (by norm_num : (1:ℝ)<2)).comp
    (tendsto_add_atTop_nat 2)
  convert h.const_mul 4 using 1
  · funext security
    simp only [_root_.CurrentAFT.Parameters.base, Nat.cast_add, Nat.cast_ofNat]
    norm_num
    ring
  · norm_num
open _root_.P2Mb608f3c5 renaming h66 → _p2mH66
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h68 (constant : ℝ) (degree accuracyOrder : ℕ) :
    ∀ᶠ security : ℕ in atTop,
      constant*(_root_.CurrentAFT.Parameters.base security:ℝ)^degree/(2:ℝ)^security ≤ _root_.CurrentAFT.inversePower security accuracyOrder := by
  have ht : Tendsto (fun security : ℕ => constant*((_root_.CurrentAFT.Parameters.base security:ℝ)^(degree+accuracyOrder)/(2:ℝ)^security))
      atTop (𝓝 0) := by simpa only [mul_zero] using (_p2mH66 (degree+accuracyOrder)).const_mul constant
  have h := ht.eventually_le_const (by norm_num : (0:ℝ)<1)
  filter_upwards [h] with security hbound
  have hb := _root_.CurrentAFT.FirstResponse.base_pos security
  unfold _root_.CurrentAFT.inversePower
  apply (le_div_iff₀ (pow_pos hb accuracyOrder)).mpr
  convert hbound using 1
  rw [pow_add]
  ring
open _root_.P2Mb608f3c5 renaming h68 → _p2mH68
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h71 :
    ∀ᶠ security : ℕ in atTop,
      1/(2:ℝ)^security ≤ 1/(4*(_root_.CurrentAFT.Parameters.base security:ℝ)) := by
  filter_upwards [_p2mH68 4 1 0] with security h
  have hb := _root_.CurrentAFT.FirstResponse.base_pos security
  apply (le_div_iff₀ (by positivity : (0:ℝ)<4*Parameters.base security)).mpr
  simpa only [_root_.CurrentAFT.inversePower, pow_zero, div_one, pow_one, mul_comm, one_div, mul_assoc, div_eq_mul_inv,
    inv_one, one_mul, mul_one] using h
open _root_.P2Mb608f3c5 renaming h71 → _p2mH71
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h70 :
    ∀ᶠ security : ℕ in atTop,
      64*(_root_.CurrentAFT.Parameters.base security:ℝ)*_root_.CurrentAFT.Parameters.dimension security*(1/(2:ℝ)^security) ≤
        1/(4*(_root_.CurrentAFT.Parameters.modulus security:ℝ)) := by
  filter_upwards [_p2mH68 (256*131072*131074) 225 0] with security h
  have hq := _root_.CurrentAFT.FirstResponse.modulus_pos security
  have hqUpper : (_root_.CurrentAFT.Parameters.modulus security:ℝ) ≤ 131072*(_root_.CurrentAFT.Parameters.base security:ℝ)^64 := by
    exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_bounds security).2
  have hdUpper : (_root_.CurrentAFT.Parameters.dimension security:ℝ) ≤ 131074*(_root_.CurrentAFT.Parameters.base security:ℝ)^160 := by
    exact_mod_cast (_root_.CurrentAFT.Parameters.dimension_bounds security).2
  have hc : (4*(_root_.CurrentAFT.Parameters.modulus security:ℝ))*(64*(_root_.CurrentAFT.Parameters.base security:ℝ)*_root_.CurrentAFT.Parameters.dimension security) ≤
      (256*131072*131074)*(_root_.CurrentAFT.Parameters.base security:ℝ)^225 := by
    calc
      _ = 256*(_root_.CurrentAFT.Parameters.modulus security:ℝ)*(_root_.CurrentAFT.Parameters.base security:ℝ)*_root_.CurrentAFT.Parameters.dimension security := by ring
      _ ≤ 256*(131072*(_root_.CurrentAFT.Parameters.base security:ℝ)^64)*(_root_.CurrentAFT.Parameters.base security:ℝ)*
          (131074*(_root_.CurrentAFT.Parameters.base security:ℝ)^160) := by gcongr
      _ = _ := by ring_nf
  apply (le_div_iff₀ (by positivity : (0:ℝ)<4*Parameters.modulus security)).mpr
  calc
    _ = ((4*(_root_.CurrentAFT.Parameters.modulus security:ℝ))*(64*(_root_.CurrentAFT.Parameters.base security:ℝ)*_root_.CurrentAFT.Parameters.dimension security))/(2:ℝ)^security := by ring
    _ ≤ ((256*131072*131074)*(_root_.CurrentAFT.Parameters.base security:ℝ)^225)/(2:ℝ)^security :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ ≤ 1 := by simpa only [_root_.CurrentAFT.inversePower, pow_zero, div_one] using h
open _root_.P2Mb608f3c5 renaming h70 → _p2mH70
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h67 :
    ∀ᶠ security : ℕ in atTop, _root_.CurrentAFT.RationalFirstResponseProgram.PrecisionBudget security security := by
  filter_upwards [_p2mH68 (16*(8*131072+2)) 65 0] with security h
  have hb := _root_.CurrentAFT.FirstResponse.base_pos security
  have hb1 : (1:ℝ) ≤ _root_.CurrentAFT.Parameters.base security := by
    exact_mod_cast (_root_.CurrentAFT.Parameters.base_ge_two security).trans' (by norm_num)
  have hpower : (1:ℝ) ≤ (_root_.CurrentAFT.Parameters.base security:ℝ)^64 := one_le_pow₀ hb1
  have hqUpper : (_root_.CurrentAFT.Parameters.modulus security:ℝ) ≤ 131072*(_root_.CurrentAFT.Parameters.base security:ℝ)^64 := by
    exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_bounds security).2
  have hc : (16*(_root_.CurrentAFT.Parameters.base security:ℝ))*(8*(_root_.CurrentAFT.Parameters.modulus security:ℝ)+2) ≤
      (16*(8*131072+2))*(_root_.CurrentAFT.Parameters.base security:ℝ)^65 := by
    calc
      _ ≤ (16*(_root_.CurrentAFT.Parameters.base security:ℝ))*(8*(131072*(_root_.CurrentAFT.Parameters.base security:ℝ)^64)+2*(_root_.CurrentAFT.Parameters.base security:ℝ)^64) := by
        gcongr
        nlinarith
      _ = _ := by ring_nf
  unfold _root_.CurrentAFT.RationalFirstResponseProgram.PrecisionBudget
  apply (le_div_iff₀ (by positivity : (0:ℝ)<16*Parameters.base security)).mpr
  calc
    _ = ((16*(_root_.CurrentAFT.Parameters.base security:ℝ))*(8*(_root_.CurrentAFT.Parameters.modulus security:ℝ)+2))/(2:ℝ)^security := by ring
    _ ≤ ((16*(8*131072+2))*(_root_.CurrentAFT.Parameters.base security:ℝ)^65)/(2:ℝ)^security :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ ≤ 1 := by simpa only [_root_.CurrentAFT.inversePower, pow_zero, div_one] using h
open _root_.P2Mb608f3c5 renaming h67 → _p2mH67
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h69 :
    ∀ᶠ security : ℕ in atTop,
      1/(2:ℝ)^security ≤ 1/(4*(_root_.CurrentAFT.Parameters.base security:ℝ)) ∧
      64*(_root_.CurrentAFT.Parameters.base security:ℝ)*_root_.CurrentAFT.Parameters.dimension security*(1/(2:ℝ)^security) ≤
        1/(4*(_root_.CurrentAFT.Parameters.modulus security:ℝ)) ∧
      _root_.CurrentAFT.RationalFirstResponseProgram.PrecisionBudget security security := by
  filter_upwards [_p2mH71, _p2mH70, _p2mH67]
    with security hs hp hf
  exact ⟨hs, hp, hf⟩
open _root_.P2Mb608f3c5 renaming h69 → _p2mH69
end
open _root_.P2Mb608f3c5 renaming h66 → _p2mH66
open _root_.P2Mb608f3c5 renaming h67 → _p2mH67
open _root_.P2Mb608f3c5 renaming h68 → _p2mH68
open _root_.P2Mb608f3c5 renaming h69 → _p2mH69
open _root_.P2Mb608f3c5 renaming h70 → _p2mH70
open _root_.P2Mb608f3c5 renaming h71 → _p2mH71
end CurrentAFT.NumericReferenceBudgets
open _root_.P2Mb608f3c5 renaming h66 → _p2mH66
open _root_.P2Mb608f3c5 renaming h67 → _p2mH67
open _root_.P2Mb608f3c5 renaming h68 → _p2mH68
open _root_.P2Mb608f3c5 renaming h69 → _p2mH69
open _root_.P2Mb608f3c5 renaming h70 → _p2mH70
open _root_.P2Mb608f3c5 renaming h71 → _p2mH71
end
open _root_.P2Mb608f3c5 renaming h66 → _p2mH66
open _root_.P2Mb608f3c5 renaming h67 → _p2mH67
open _root_.P2Mb608f3c5 renaming h68 → _p2mH68
open _root_.P2Mb608f3c5 renaming h69 → _p2mH69
open _root_.P2Mb608f3c5 renaming h70 → _p2mH70
open _root_.P2Mb608f3c5 renaming h71 → _p2mH71
namespace CurrentAFT.NumericalPopulationConstants
end CurrentAFT.NumericalPopulationConstants
namespace CurrentAFT.RationalBackgroundPopulationProgram.errorConstant
end CurrentAFT.RationalBackgroundPopulationProgram.errorConstant
namespace CurrentAFT.RationalBackgroundPopulationProgram.freeQueueBound
end CurrentAFT.RationalBackgroundPopulationProgram.freeQueueBound
namespace CurrentAFT.RationalBackgroundPopulationProgram.freeQueueError
end CurrentAFT.RationalBackgroundPopulationProgram.freeQueueError
namespace CurrentAFT.RationalBackgroundPopulationProgram.legAtomBound
end CurrentAFT.RationalBackgroundPopulationProgram.legAtomBound
namespace CurrentAFT.RationalPopulationApproximation.error
end CurrentAFT.RationalPopulationApproximation.error
section
namespace CurrentAFT.RationalBackgroundPopulationProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies
open RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  ProposalPrimary.primaryLaw bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h94 (security order : ℕ) : 0≤_root_.CurrentAFT.RationalBackgroundPopulationProgram.bound security order := by
  rcases _p2mH95 security order with ⟨hf,hq,hl,_,_,_⟩
  unfold _root_.CurrentAFT.RationalBackgroundPopulationProgram.bound _root_.CurrentAFT.RationalBackgroundPopulationProgram.freeQueueBound
  positivity
open _root_.P2Mb608f3c5 renaming h94 → _p2mH94
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h93 (security order : ℕ) (horder : 2≤order) (queue : ℤ)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |(_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder queue arity).val colors centers|≤_root_.CurrentAFT.RationalBackgroundPopulationProgram.bound security order := by
  rcases _p2mH95 security order with ⟨hf,hq,hl,_,_,_⟩
  have hFQ : ∀ arity colors centers,
      |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.GradedControlAlgebra.familyProduct (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
        (_root_.CurrentAFT.RationalBackgroundPopulationProgram.freeActual security order horder) (_root_.CurrentAFT.RationalBackgroundPopulationProgram.queueActual security order horder queue)) arity colors centers|≤_root_.CurrentAFT.RationalBackgroundPopulationProgram.freeQueueBound security order := by
    intro arity colors centers
    rw [← _p2mH86]
    exact (_p2mH119 order _ _ _ _ hf hq (_p2mH97 security order horder)
      (_p2mH100 security order horder queue) arity colors centers).trans_eq (by unfold _root_.CurrentAFT.RationalBackgroundPopulationProgram.freeQueueBound; ring)
  have hFQ0 : 0≤_root_.CurrentAFT.RationalBackgroundPopulationProgram.freeQueueBound security order := by unfold _root_.CurrentAFT.RationalBackgroundPopulationProgram.freeQueueBound; positivity
  change |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.GradedControlAlgebra.familyProduct (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
    (_root_.CurrentAFT.GradedControlAlgebra.familyProduct (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
      (_root_.CurrentAFT.RationalBackgroundPopulationProgram.freeActual security order horder) (_root_.CurrentAFT.RationalBackgroundPopulationProgram.queueActual security order horder queue))
    (_root_.CurrentAFT.RationalBackgroundPopulationProgram.legActual security order horder)) arity colors centers|≤_
  rw [← _p2mH86]
  exact _p2mH119 order _ _ _ _ hFQ0 hl hFQ (_p2mH99 security order horder) arity colors centers
open _root_.P2Mb608f3c5 renaming h93 → _p2mH93
end
open _root_.P2Mb608f3c5 renaming h93 → _p2mH93
open _root_.P2Mb608f3c5 renaming h94 → _p2mH94
end CurrentAFT.RationalBackgroundPopulationProgram
open _root_.P2Mb608f3c5 renaming h93 → _p2mH93
open _root_.P2Mb608f3c5 renaming h94 → _p2mH94
namespace CurrentAFT.NumericalPopulationConstants
open AFT PolynomialErrorEnvelope
noncomputable section
end
end CurrentAFT.NumericalPopulationConstants
end
open _root_.P2Mb608f3c5 renaming h93 → _p2mH93
open _root_.P2Mb608f3c5 renaming h94 → _p2mH94
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedScalarFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedScalarSafeDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedScalarSumDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h154 (security r s : ℕ) :
    0 ≤ _root_.CurrentAFT.WeightedPointKernelProgram.errorConstant security r s := by
  unfold _root_.CurrentAFT.WeightedPointKernelProgram.errorConstant _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant
  positivity
open _root_.P2Mb608f3c5 renaming h154 → _p2mH154
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h158 (security r s count tags : ℕ) : 0 ≤ _root_.CurrentAFT.RationalPackedRootProgram.scalarError security r s count tags := by
  unfold _root_.CurrentAFT.RationalPackedRootProgram.scalarError
  have h := _p2mH154 security r s
  positivity
open _root_.P2Mb608f3c5 renaming h158 → _p2mH158
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h157 (security r s tags : ℕ) : 0 ≤ _root_.CurrentAFT.RationalPackedRootProgram.scalarBound security r s tags := by
  unfold _root_.CurrentAFT.RationalPackedRootProgram.scalarBound
  have h := _p2mH154 security r s
  positivity
open _root_.P2Mb608f3c5 renaming h157 → _p2mH157
end
open _root_.P2Mb608f3c5 renaming h154 → _p2mH154
open _root_.P2Mb608f3c5 renaming h157 → _p2mH157
open _root_.P2Mb608f3c5 renaming h158 → _p2mH158
end CurrentAFT.RationalPackedRootProgram
open _root_.P2Mb608f3c5 renaming h154 → _p2mH154
open _root_.P2Mb608f3c5 renaming h157 → _p2mH157
open _root_.P2Mb608f3c5 renaming h158 → _p2mH158
end
open _root_.P2Mb608f3c5 renaming h154 → _p2mH154
open _root_.P2Mb608f3c5 renaming h157 → _p2mH157
open _root_.P2Mb608f3c5 renaming h158 → _p2mH158
namespace CurrentAFT.RationalRootGroupProgram
end CurrentAFT.RationalRootGroupProgram
namespace CurrentAFT.RationalRootGroupProgram.LocalRole
end CurrentAFT.RationalRootGroupProgram.LocalRole
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.center
end CurrentAFT.RationalRootGroupProgram.LocalRole.center
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.leg
end CurrentAFT.RationalRootGroupProgram.LocalRole.leg
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.ordinary
end CurrentAFT.RationalRootGroupProgram.LocalRole.ordinary
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.primary
end CurrentAFT.RationalRootGroupProgram.LocalRole.primary
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.queue
end CurrentAFT.RationalRootGroupProgram.LocalRole.queue
namespace CurrentAFT.RationalRootGroupProgram.localTable
end CurrentAFT.RationalRootGroupProgram.localTable
namespace CurrentAFT.RationalRootGroupProgram.localTable.match_1
end CurrentAFT.RationalRootGroupProgram.localTable.match_1
namespace CurrentAFT.RationalRootGroupProgram.role
end CurrentAFT.RationalRootGroupProgram.role
namespace CurrentAFT.RationalRootGroupProgram.role.match_3
end CurrentAFT.RationalRootGroupProgram.role.match_3
namespace CurrentAFT.RationalRootGroupProgram.sourceNatural
end CurrentAFT.RationalRootGroupProgram.sourceNatural
namespace CurrentAFT.RationalRootGroupProgram.sourceNatural.match_1
end CurrentAFT.RationalRootGroupProgram.sourceNatural.match_1
namespace CurrentAFT.RationalRootGroupProgram.table
end CurrentAFT.RationalRootGroupProgram.table
namespace CurrentAFT.RootReferenceColumns.legAt
end CurrentAFT.RootReferenceColumns.legAt
namespace CurrentAFT.RootReferenceColumns.reducedColumn.match_1
end CurrentAFT.RootReferenceColumns.reducedColumn.match_1
namespace CurrentAFT.RootReferenceColumns.singletonAt
end CurrentAFT.RootReferenceColumns.singletonAt
namespace CurrentAFT.RootReferenceColumns.unselectedAt.match_1
end CurrentAFT.RootReferenceColumns.unselectedAt.match_1
section
namespace CurrentAFT.RationalRootGroupProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalRootGroupProgram.groupBoundsFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalRootGroupProgram.groupBoundsSafeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h186 (security order : ℕ) : 1 ≤ _root_.CurrentAFT.RationalRootGroupProgram.pointBound security order := by
  unfold _root_.CurrentAFT.RationalRootGroupProgram.pointBound
  linarith [abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.primaryBound security order), abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.ordinaryBound security order),
    abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.legBound security order), abs_nonneg (_root_.CurrentAFT.RationalRootGroupProgram.singletonBound security order)]
open _root_.P2Mb608f3c5 renaming h186 → _p2mH186
end
open _root_.P2Mb608f3c5 renaming h186 → _p2mH186
end CurrentAFT.RationalRootGroupProgram
open _root_.P2Mb608f3c5 renaming h186 → _p2mH186
end
open _root_.P2Mb608f3c5 renaming h186 → _p2mH186
namespace CurrentAFT.OrdinaryRaising.positiveInverse
end CurrentAFT.OrdinaryRaising.positiveInverse
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRectangleIndex RationalRootGroupProgram CycleRootExpansion ActualControls
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedProductFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h152 (security order : ℕ) : 1 ≤ _root_.CurrentAFT.RationalPackedRootProgram.localGrowth security order :=
  _p2mH109 _ _ _ ((by norm_num : (0 : ℝ) ≤ 1).trans (_p2mH186 security order))
    (_p2mH185 security order)
open _root_.P2Mb608f3c5 renaming h152 → _p2mH152
end
open _root_.P2Mb608f3c5 renaming h152 → _p2mH152
end CurrentAFT.RationalPackedRootProgram
open _root_.P2Mb608f3c5 renaming h152 → _p2mH152
end
open _root_.P2Mb608f3c5 renaming h152 → _p2mH152
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
  ControlCoordinates GradedControlAlgebra RationalActualFamilyApproximation
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedApproxFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedApproxSafeDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedApproxSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedApproxSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h159 (security order r s count tags : ℕ) :
    0 ≤ _root_.CurrentAFT.RationalPackedRootProgram.sourceError security order r s count tags := by
  unfold _root_.CurrentAFT.RationalPackedRootProgram.sourceError
  have hs := _p2mH157 security r s tags
  have he := _p2mH158 security r s count tags
  have hE := _p2mH185 security order
  have hC := (by norm_num : (0:ℝ)≤1).trans (_p2mH152 security order)
  positivity
open _root_.P2Mb608f3c5 renaming h159 → _p2mH159
end
open _root_.P2Mb608f3c5 renaming h159 → _p2mH159
end CurrentAFT.RationalPackedRootProgram
open _root_.P2Mb608f3c5 renaming h159 → _p2mH159
end
open _root_.P2Mb608f3c5 renaming h159 → _p2mH159
namespace CurrentAFT.LocalCoefficientPointBounds
end CurrentAFT.LocalCoefficientPointBounds
namespace CurrentAFT.LocalCoefficientPointBounds.selectedBound
end CurrentAFT.LocalCoefficientPointBounds.selectedBound
namespace CurrentAFT.NumericalGroupConstants
end CurrentAFT.NumericalGroupConstants
namespace CurrentAFT.RationalCoefficientExtraction
end CurrentAFT.RationalCoefficientExtraction
namespace CurrentAFT.RationalCoefficientExtraction.atomErrorConstant
end CurrentAFT.RationalCoefficientExtraction.atomErrorConstant
namespace CurrentAFT.RationalCoefficientExtraction.extractionBound
end CurrentAFT.RationalCoefficientExtraction.extractionBound
namespace CurrentAFT.RationalCoefficientExtraction.extractionError
end CurrentAFT.RationalCoefficientExtraction.extractionError
namespace CurrentAFT.RationalCoefficientExtraction.normalizedError
end CurrentAFT.RationalCoefficientExtraction.normalizedError
namespace CurrentAFT.RationalNormalizedPrimaryProgram
end CurrentAFT.RationalNormalizedPrimaryProgram
namespace CurrentAFT.RationalNormalizedPrimaryProgram.inverseBound
end CurrentAFT.RationalNormalizedPrimaryProgram.inverseBound
namespace CurrentAFT.RationalNormalizedPrimaryProgram.inverseErrorConstant
end CurrentAFT.RationalNormalizedPrimaryProgram.inverseErrorConstant
namespace CurrentAFT.RationalNormalizedPrimaryProgram.primaryErrorConstant
end CurrentAFT.RationalNormalizedPrimaryProgram.primaryErrorConstant
namespace CurrentAFT.RationalOrdinaryFamilyProgram.atRootBound
end CurrentAFT.RationalOrdinaryFamilyProgram.atRootBound
namespace CurrentAFT.RationalOrdinaryFamilyProgram.atRootError
end CurrentAFT.RationalOrdinaryFamilyProgram.atRootError
namespace CurrentAFT.RationalOrdinaryFamilyProgram.errorConstant
end CurrentAFT.RationalOrdinaryFamilyProgram.errorConstant
namespace CurrentAFT.RationalOrdinaryFamilyProgram.independentError
end CurrentAFT.RationalOrdinaryFamilyProgram.independentError
namespace CurrentAFT.RationalOrdinaryFamilyProgram.meanError
end CurrentAFT.RationalOrdinaryFamilyProgram.meanError
namespace CurrentAFT.RationalOrdinaryProfileProgram
end CurrentAFT.RationalOrdinaryProfileProgram
namespace CurrentAFT.RationalOrdinaryProfileProgram.profileErrorConstant
end CurrentAFT.RationalOrdinaryProfileProgram.profileErrorConstant
namespace CurrentAFT.RationalPackedRootProgram.current
end CurrentAFT.RationalPackedRootProgram.current
namespace CurrentAFT.RationalPackedRootProgram.productActual
end CurrentAFT.RationalPackedRootProgram.productActual
namespace CurrentAFT.RationalPackedRootProgram.rawErrorConstant
end CurrentAFT.RationalPackedRootProgram.rawErrorConstant
namespace CurrentAFT.RationalPackedRootProgram.summand
end CurrentAFT.RationalPackedRootProgram.summand
namespace CurrentAFT.RationalRootGroupProgram.errorConstant
end CurrentAFT.RationalRootGroupProgram.errorConstant
namespace CurrentAFT.RationalRootGroupProgram.legBound
end CurrentAFT.RationalRootGroupProgram.legBound
namespace CurrentAFT.RationalRootGroupProgram.ordinaryBound
end CurrentAFT.RationalRootGroupProgram.ordinaryBound
namespace CurrentAFT.RationalRootGroupProgram.pointBound
end CurrentAFT.RationalRootGroupProgram.pointBound
namespace CurrentAFT.RationalRootGroupProgram.primaryBound
end CurrentAFT.RationalRootGroupProgram.primaryBound
namespace CurrentAFT.RationalRootGroupProgram.singletonBound
end CurrentAFT.RationalRootGroupProgram.singletonBound
namespace CurrentAFT.RationalRootMassProgram
end CurrentAFT.RationalRootMassProgram
namespace CurrentAFT.RationalRootMassProgram.fixedErrorConstant
end CurrentAFT.RationalRootMassProgram.fixedErrorConstant
namespace CurrentAFT.RationalRootMassProgram.primaryMassErrorConstant
end CurrentAFT.RationalRootMassProgram.primaryMassErrorConstant
namespace CurrentAFT.RationalRootMassProgram.weightedErrorConstant
end CurrentAFT.RationalRootMassProgram.weightedErrorConstant
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
  GradedControlAlgebra RationalActualFamilyApproximation PolynomialErrorEnvelope
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedRatesFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedRatesSafeDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedRatesSumDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h151 (security order : ℕ) : 0 ≤ _root_.CurrentAFT.RationalPackedRootProgram.kernelErrorBound security order := by
  unfold _root_.CurrentAFT.RationalPackedRootProgram.kernelErrorBound _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant
  positivity
open _root_.P2Mb608f3c5 renaming h151 → _p2mH151
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h150 (security order : ℕ) : 0 ≤ _root_.CurrentAFT.RationalPackedRootProgram.errorConstant security order := by
  have hk := _p2mH151 security order
  have hE := _p2mH185 security order
  have hC := (by norm_num : (0:ℝ)≤1).trans (_p2mH152 security order)
  unfold _root_.CurrentAFT.RationalPackedRootProgram.errorConstant _root_.CurrentAFT.RationalPackedRootProgram.uniformScalarBound _root_.CurrentAFT.RationalPackedRootProgram.uniformScalarError
  positivity
open _root_.P2Mb608f3c5 renaming h150 → _p2mH150
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h153 (security order r s : ℕ) (hdegree : r+s≤order) :
    _root_.CurrentAFT.WeightedPointKernelProgram.errorConstant security r s ≤ _root_.CurrentAFT.RationalPackedRootProgram.kernelErrorBound security order := by
  have hp : 0 ≤ _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant security := by
    unfold _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant; positivity
  have hb : 0 ≤ _root_.CurrentAFT.RationalRootMassProgram.primaryErrorConstant security*_root_.CurrentAFT.Parameters.modulus security+2 := by positivity
  have hr : (r:ℝ)≤order := by exact_mod_cast (show r≤order by omega)
  have hs : (s:ℝ)≤order := by exact_mod_cast (show s≤order by omega)
  unfold _root_.CurrentAFT.WeightedPointKernelProgram.errorConstant _root_.CurrentAFT.RationalPackedRootProgram.kernelErrorBound
  nlinarith [mul_le_mul_of_nonneg_right hr hp, mul_le_mul_of_nonneg_right hs hb]
open _root_.P2Mb608f3c5 renaming h153 → _p2mH153
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h155 (security order r s count tags : ℕ) (hdegree : r+s≤order)
    (hcount : count≤2*order) (htags : tags≤order) :
    _root_.CurrentAFT.RationalPackedRootProgram.rawErrorConstant security order r s count tags ≤ _root_.CurrentAFT.RationalPackedRootProgram.errorConstant security order := by
  have hE := _p2mH185 security order
  have hK := _p2mH154 security r s
  have hU := _p2mH151 security order
  have hC := _p2mH152 security order
  have hKle := _p2mH153 security order r s hdegree
  have hcountR : (count:ℝ)≤2*order := by exact_mod_cast hcount
  have htagsR : (tags:ℝ)≤order := by exact_mod_cast htags
  have hsb : _root_.CurrentAFT.RationalPackedRootProgram.scalarBound security r s tags ≤ _root_.CurrentAFT.RationalPackedRootProgram.uniformScalarBound security order := by
    unfold _root_.CurrentAFT.RationalPackedRootProgram.scalarBound _root_.CurrentAFT.RationalPackedRootProgram.uniformScalarBound
    gcongr
  have hse : _root_.CurrentAFT.RationalPackedRootProgram.scalarError security r s count tags ≤ _root_.CurrentAFT.RationalPackedRootProgram.uniformScalarError security order := by
    unfold _root_.CurrentAFT.RationalPackedRootProgram.scalarError _root_.CurrentAFT.RationalPackedRootProgram.uniformScalarError
    have hfirst : _root_.CurrentAFT.WeightedPointKernelProgram.errorConstant security r s+4*count ≤
        _root_.CurrentAFT.RationalPackedRootProgram.kernelErrorBound security order+8*order := by linarith
    have hsecond : (1:ℝ)+4*tags≤1+4*order := by linarith
    exact add_le_add (mul_le_mul hfirst hsecond (by positivity) (by positivity)) (by linarith)
  have hSB : 0 ≤ _root_.CurrentAFT.RationalPackedRootProgram.uniformScalarBound security order := by unfold _root_.CurrentAFT.RationalPackedRootProgram.uniformScalarBound; positivity
  have hpre : _root_.CurrentAFT.RationalPackedRootProgram.scalarBound security r s tags*count*_root_.CurrentAFT.RationalRootGroupProgram.errorConstant security order+
      _root_.CurrentAFT.RationalPackedRootProgram.scalarError security r s count tags ≤
      _root_.CurrentAFT.RationalPackedRootProgram.uniformScalarBound security order*(2*order)*_root_.CurrentAFT.RationalRootGroupProgram.errorConstant security order+
        _root_.CurrentAFT.RationalPackedRootProgram.uniformScalarError security order := by
    gcongr
  have hpow := pow_le_pow_right₀ hC hcount
  have hsource : _root_.CurrentAFT.RationalPackedRootProgram.sourceError security order r s count tags ≤
      (_root_.CurrentAFT.RationalPackedRootProgram.uniformScalarBound security order*(2*order)*_root_.CurrentAFT.RationalRootGroupProgram.errorConstant security order+
        _root_.CurrentAFT.RationalPackedRootProgram.uniformScalarError security order)*(_root_.CurrentAFT.RationalPackedRootProgram.localGrowth security order)^(2*order) := by
    unfold _root_.CurrentAFT.RationalPackedRootProgram.sourceError
    exact mul_le_mul hpre hpow (pow_nonneg ((by norm_num : (0:ℝ)≤1).trans hC) _) (by
      unfold _root_.CurrentAFT.RationalPackedRootProgram.uniformScalarBound _root_.CurrentAFT.RationalPackedRootProgram.uniformScalarError; positivity)
  have hq : (1:ℝ)≤_root_.CurrentAFT.CurrentRectangleIndex.colors security := by
    exact_mod_cast _root_.CurrentAFT.CurrentRectangleIndex.colors_pos security
  have hqpow : (_root_.CurrentAFT.CurrentRectangleIndex.colors security:ℝ)^(count*3) ≤
      (_root_.CurrentAFT.CurrentRectangleIndex.colors security:ℝ)^(6*order) :=
    pow_le_pow_right₀ hq (by omega)
  unfold _root_.CurrentAFT.RationalPackedRootProgram.rawErrorConstant _root_.CurrentAFT.RationalPackedRootProgram.errorConstant
  exact mul_le_mul hqpow hsource (_p2mH159 _ _ _ _ _ _) (by positivity)
open _root_.P2Mb608f3c5 renaming h155 → _p2mH155
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h149 {security r s : ℕ} (bits order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) (hroom : tagged.card ≤ _root_.CurrentAFT.Parameters.bodySize security)
    (hdegree : r+s≤order) (htags : tagged.card≤order)
    (sourcePrimary : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (sourceBody : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security)
    (hfirst : _root_.CurrentAFT.RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(_root_.CurrentAFT.Parameters.base security:ℝ)))
    (hbudget : 64*(_root_.CurrentAFT.Parameters.base security:ℝ)*_root_.CurrentAFT.Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(_root_.CurrentAFT.Parameters.modulus security:ℝ)))
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.ActualControls.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (_root_.CurrentAFT.RationalPackedRootProgram.current security bits order queue (_root_.CurrentAFT.RationalPackedRootProgram.actualMetadata selection tagged)
        (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)) arity colors centers -
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.ActualRootResponse.response order horder queue selection tagged layout
        (_root_.CurrentAFT.WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)) arity colors centers| ≤
      _root_.CurrentAFT.RationalPackedRootProgram.errorConstant security order*(1/(2:ℝ)^bits) := by
  have hc : _root_.CurrentAFT.RationalPackedRootProgram.groupCount selection tagged≤2*order := by
    have hk := _p2mH41 selection tagged
    unfold _root_.CurrentAFT.RationalPackedRootProgram.groupCount
    omega
  exact (current_error_raw bits order horder queue selection tagged layout hroom sourcePrimary sourceBody
    hfirst hprecision hbudget arity colors centers).trans
    (mul_le_mul_of_nonneg_right (_p2mH155 security order r s _ _ hdegree hc htags) (by positivity))
open _root_.P2Mb608f3c5 renaming h149 → CurrentAFT.RationalPackedRootProgram.current_error
open _root_.P2Mb608f3c5 renaming h149 → _p2mH149
end
open _root_.P2Mb608f3c5 renaming h149 → CurrentAFT.RationalPackedRootProgram.current_error
open _root_.P2Mb608f3c5 renaming h149 → _p2mH149
open _root_.P2Mb608f3c5 renaming h150 → _p2mH150
open _root_.P2Mb608f3c5 renaming h151 → _p2mH151
open _root_.P2Mb608f3c5 renaming h153 → _p2mH153
open _root_.P2Mb608f3c5 renaming h155 → _p2mH155
end CurrentAFT.RationalPackedRootProgram
open _root_.P2Mb608f3c5 renaming h149 → CurrentAFT.RationalPackedRootProgram.current_error
open _root_.P2Mb608f3c5 renaming h149 → _p2mH149
open _root_.P2Mb608f3c5 renaming h150 → _p2mH150
open _root_.P2Mb608f3c5 renaming h151 → _p2mH151
open _root_.P2Mb608f3c5 renaming h153 → _p2mH153
open _root_.P2Mb608f3c5 renaming h155 → _p2mH155
end
open _root_.P2Mb608f3c5 renaming h149 → CurrentAFT.RationalPackedRootProgram.current_error
open _root_.P2Mb608f3c5 renaming h149 → _p2mH149
open _root_.P2Mb608f3c5 renaming h150 → _p2mH150
open _root_.P2Mb608f3c5 renaming h151 → _p2mH151
open _root_.P2Mb608f3c5 renaming h153 → _p2mH153
open _root_.P2Mb608f3c5 renaming h155 → _p2mH155
namespace CurrentAFT.RationalPackedRootProgram.errorConstant
end CurrentAFT.RationalPackedRootProgram.errorConstant
namespace CurrentAFT.RationalPackedRootProgram.kernelErrorBound
end CurrentAFT.RationalPackedRootProgram.kernelErrorBound
namespace CurrentAFT.RationalPackedRootProgram.localGrowth
end CurrentAFT.RationalPackedRootProgram.localGrowth
namespace CurrentAFT.RationalPackedRootProgram.uniformScalarBound
end CurrentAFT.RationalPackedRootProgram.uniformScalarBound
namespace CurrentAFT.RationalPackedRootProgram.uniformScalarError
end CurrentAFT.RationalPackedRootProgram.uniformScalarError
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
  GradedControlAlgebra RationalActualFamilyApproximation
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedBoundFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedBoundSafeDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedBoundSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedBoundSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h156 (security order : ℕ) : 0 ≤ _root_.CurrentAFT.RationalPackedRootProgram.responseBound security order := by
  unfold _root_.CurrentAFT.RationalPackedRootProgram.responseBound
  have hc := (by norm_num : (0:ℝ)≤1).trans (_p2mH152 security order)
  positivity
open _root_.P2Mb608f3c5 renaming h156 → _p2mH156
end
open _root_.P2Mb608f3c5 renaming h156 → _p2mH156
end CurrentAFT.RationalPackedRootProgram
open _root_.P2Mb608f3c5 renaming h156 → _p2mH156
end
open _root_.P2Mb608f3c5 renaming h156 → _p2mH156
namespace CurrentAFT.RationalPackedRootProgram.responseBound
end CurrentAFT.RationalPackedRootProgram.responseBound
section
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock TaggedSelection GradedControlAlgebra LocalCoefficientFamily
  ActualControls ProposalPrimary ControlCoordinates ControlProduct CanonicalReconstruction
  UniformTaggedOutput ActualRootFamily FullResponsePointFormula RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  primaryLaw bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h140 (security order : ℕ) : 1+((_root_.CurrentAFT.RationalFullResponseProgram.tags security order).card:ℝ) ≤ _root_.CurrentAFT.RationalFullResponseProgram.tagCountBound security order := by
  have hb : 1 ≤ Fintype.card (_root_.CurrentAFT.ActualBlockFock.BlockIndex security) := by
    rw [_p2mH49]
    have h := _p2mH43 security
    omega
  have h := (Finset.card_filter_le (s := _root_.CurrentAFT.FullResponseEnumeration.boundedSubsets (_root_.CurrentAFT.ActualBlockFock.BlockIndex security) order)
    (p := fun tagged => 2 ≤ tagged.card)).trans (_p2mH50 order hb)
  rw [_p2mH49] at h
  unfold _root_.CurrentAFT.RationalFullResponseProgram.tagCountBound _root_.CurrentAFT.RationalFullResponseProgram.tags
  exact_mod_cast Nat.add_le_add_left h 1
open _root_.P2Mb608f3c5 renaming h140 → _p2mH140
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h141 {security order : ℕ} {tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)} (h : tagged ∈ _root_.CurrentAFT.RationalFullResponseProgram.tags security order) :
    tagged.card ≤ order := (_p2mH51 order tagged).mp (Finset.mem_filter.mp h).1
open _root_.P2Mb608f3c5 renaming h141 → _p2mH141
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h137 {Index : Type*} (indices : Finset Index) (first : ℝ) (terms : Index → ℝ)
    (bound : ℝ) (hfirst : |first| ≤ bound) (hterms : ∀ index ∈ indices, |terms index| ≤ bound) :
    |first+∑ index ∈ indices, terms index| ≤ (1+(indices.card:ℝ))*bound := by
  have hs := (Finset.abs_sum_le_sum_abs terms indices).trans (Finset.sum_le_sum hterms)
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  exact (abs_add_le _ _).trans ((add_le_add hfirst hs).trans_eq (by ring))
open _root_.P2Mb608f3c5 renaming h137 → _p2mH137
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h138 (security bits order : ℕ) (horder : 1 ≤ order) (hroom : order ≤ _root_.CurrentAFT.Parameters.bodySize security) (queue : ℤ)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) (chosen : _root_.CurrentAFT.TaggedSelection.Selection security source.1.val.1.val source.1.val.2.val)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (hfirst : _root_.CurrentAFT.RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(_root_.CurrentAFT.Parameters.base security:ℝ)))
    (hbudget : 64*(_root_.CurrentAFT.Parameters.base security:ℝ)*_root_.CurrentAFT.Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(_root_.CurrentAFT.Parameters.modulus security:ℝ)))
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (_root_.CurrentAFT.RationalFullResponseProgram.selected bits order queue chosen (fun index => (source.2.1 index).val)
      (fun index => (source.2.2 index).val.val)) arity colors centers-
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.FullResponseWeightedIdentity.selected security order horder queue source chosen layout)
        arity colors centers| ≤ _root_.CurrentAFT.RationalFullResponseProgram.rootError security order*(1/(2:ℝ)^bits) := by
  have ht (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (htags : tagged.card ≤ order) :=
    _p2mH149 bits order horder queue chosen tagged layout (htags.trans hroom)
      source.1.property htags source.2.1 source.2.2 hfirst hprecision hbudget arity colors centers
  have h := _p2mH137 (_root_.CurrentAFT.RationalFullResponseProgram.tags security order) _ _
    (_root_.CurrentAFT.RationalPackedRootProgram.errorConstant security order*(1/(2:ℝ)^bits))
    (ht ∅ (by simp)) (fun tagged hm => ht tagged (_p2mH141 hm))
  simp only [_root_.CurrentAFT.RationalActualFamilyApproximation.interpret, _root_.CurrentAFT.RationalFamilyProductProgram.pullback, _root_.CurrentAFT.RationalFamilyProductProgram.realTable,
    _root_.CurrentAFT.RationalFullResponseProgram.selected, Rat.cast_add, Rat.cast_sum, _root_.CurrentAFT.RationalActualFamilyApproximation.data, _root_.CurrentAFT.FullResponseWeightedIdentity.selected,
    Pi.add_apply, Submodule.coe_add, Finset.sum_apply, Submodule.coe_sum, _root_.CurrentAFT.FullResponseWeightedIdentity.sourceKernel] at *
  rw [Finset.sum_sub_distrib] at h
  have h' := h.trans (mul_le_mul_of_nonneg_right (_p2mH140 security order)
    (mul_nonneg (_p2mH150 security order) (by positivity)))
  convert h' using 1 <;> first | rfl | (unfold _root_.CurrentAFT.RationalFullResponseProgram.rootError; ring) | (congr 1 <;> ring)
open _root_.P2Mb608f3c5 renaming h138 → _p2mH138
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h127 (security bits order : ℕ) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (_root_.CurrentAFT.RationalFullResponseProgram.choiceAverage security bits order source.1.val.1.val source.1.val.2.val queue
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val)) arity colors centers =
    (_root_.CurrentAFT.UniformTaggedOutput.choiceLaw security _ _ (_root_.CurrentAFT.ActualRootFamily.primary_room security order hroom source.1) (_root_.CurrentAFT.ActualRootFamily.body_room security order hroom source.1)).expectation
      (fun choice => _root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (_root_.CurrentAFT.RationalFullResponseProgram.selected bits order queue (_root_.CurrentAFT.UniformTaggedOutput.selection security _ _ choice)
        (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val)) arity colors centers) := by
  unfold _root_.CurrentAFT.RationalActualFamilyApproximation.interpret _root_.CurrentAFT.RationalFamilyProductProgram.pullback _root_.CurrentAFT.RationalFamilyProductProgram.realTable _root_.CurrentAFT.RationalFullResponseProgram.choiceAverage
  simp only [Rat.cast_div, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, _root_.AFT.FiniteDist.expectation,
    _p2mH200, Finset.sum_div, one_div, _p2mH139]
  apply Finset.sum_congr (by ext choice; simp)
  intro choice _
  ring
open _root_.P2Mb608f3c5 renaming h127 → _p2mH127
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h128 (security order : ℕ) (horder : 1 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.FullResponseWeightedIdentity.choiceAverage security order horder hroom queue source layout) arity colors centers =
    (_root_.CurrentAFT.UniformTaggedOutput.choiceLaw security _ _ (_root_.CurrentAFT.ActualRootFamily.primary_room security order hroom source.1) (_root_.CurrentAFT.ActualRootFamily.body_room security order hroom source.1)).expectation
      (fun choice => _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.FullResponseWeightedIdentity.selected security order horder queue source
        (_root_.CurrentAFT.UniformTaggedOutput.selection security _ _ choice) layout) arity colors centers) := by
  simp only [_root_.CurrentAFT.RationalActualFamilyApproximation.data, _root_.CurrentAFT.FullResponseWeightedIdentity.choiceAverage, _root_.AFT.FiniteDist.expectation, Finset.sum_apply,
    Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
open _root_.P2Mb608f3c5 renaming h128 → _p2mH128
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h129 (security bits order : ℕ) (horder : 1 ≤ order)
    (hroom : 2*order ≤ security) (hbody : order ≤ _root_.CurrentAFT.Parameters.bodySize security) (queue : ℤ)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (hfirst : _root_.CurrentAFT.RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(_root_.CurrentAFT.Parameters.base security:ℝ)))
    (hbudget : 64*(_root_.CurrentAFT.Parameters.base security:ℝ)*_root_.CurrentAFT.Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(_root_.CurrentAFT.Parameters.modulus security:ℝ)))
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (_root_.CurrentAFT.RationalFullResponseProgram.choiceAverage security bits order source.1.val.1.val source.1.val.2.val queue
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val)) arity colors centers-
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.FullResponseWeightedIdentity.choiceAverage security order horder hroom queue source layout)
        arity colors centers| ≤ _root_.CurrentAFT.RationalFullResponseProgram.rootError security order*(1/(2:ℝ)^bits) := by
  rw [_p2mH127 security bits order hroom, _p2mH128, ← _root_.AFT.FiniteDist.expectation_sub]
  exact _p2mH30 _ _ _
    (fun choice => _p2mH138 security bits order horder hbody queue source _ layout hfirst hprecision hbudget arity colors centers)
open _root_.P2Mb608f3c5 renaming h129 → _p2mH129
end
open _root_.P2Mb608f3c5 renaming h127 → _p2mH127
open _root_.P2Mb608f3c5 renaming h128 → _p2mH128
open _root_.P2Mb608f3c5 renaming h129 → _p2mH129
open _root_.P2Mb608f3c5 renaming h137 → _p2mH137
open _root_.P2Mb608f3c5 renaming h138 → _p2mH138
open _root_.P2Mb608f3c5 renaming h140 → _p2mH140
open _root_.P2Mb608f3c5 renaming h141 → _p2mH141
end CurrentAFT.RationalFullResponseProgram
open _root_.P2Mb608f3c5 renaming h127 → _p2mH127
open _root_.P2Mb608f3c5 renaming h128 → _p2mH128
open _root_.P2Mb608f3c5 renaming h129 → _p2mH129
open _root_.P2Mb608f3c5 renaming h137 → _p2mH137
open _root_.P2Mb608f3c5 renaming h138 → _p2mH138
open _root_.P2Mb608f3c5 renaming h140 → _p2mH140
open _root_.P2Mb608f3c5 renaming h141 → _p2mH141
end
open _root_.P2Mb608f3c5 renaming h127 → _p2mH127
open _root_.P2Mb608f3c5 renaming h128 → _p2mH128
open _root_.P2Mb608f3c5 renaming h129 → _p2mH129
open _root_.P2Mb608f3c5 renaming h137 → _p2mH137
open _root_.P2Mb608f3c5 renaming h138 → _p2mH138
open _root_.P2Mb608f3c5 renaming h140 → _p2mH140
open _root_.P2Mb608f3c5 renaming h141 → _p2mH141
section
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock TaggedSelection GradedControlAlgebra LocalCoefficientFamily
  ActualControls ProposalPrimary FullResponsePointFormula RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension primaryLaw bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h130 (security order : ℕ) :
    0 ≤ _root_.CurrentAFT.RationalFullResponseProgram.rootBound security order ∧ 0 ≤ _root_.CurrentAFT.RationalFullResponseProgram.rootError security order ∧
    0 ≤ _root_.CurrentAFT.RationalFullResponseProgram.fixedQueueBound security order ∧ 0 ≤ _root_.CurrentAFT.RationalFullResponseProgram.fixedQueueError security order ∧
    0 ≤ _root_.CurrentAFT.RationalFullResponseProgram.responseError security order ∧ 0 ≤ _root_.CurrentAFT.RationalFullResponseProgram.errorConstant security order := by
  have ht : 0 ≤ _root_.CurrentAFT.RationalFullResponseProgram.tagCountBound security order := by unfold _root_.CurrentAFT.RationalFullResponseProgram.tagCountBound; positivity
  have hb : 0 ≤ _root_.CurrentAFT.RationalFullResponseProgram.rootBound security order := mul_nonneg ht (_p2mH156 security order)
  have he : 0 ≤ _root_.CurrentAFT.RationalFullResponseProgram.rootError security order := mul_nonneg ht (_p2mH150 security order)
  have hfB := _p2mH94 security order
  have hfE := _p2mH96 security order
  have hB : 0 ≤ _root_.CurrentAFT.RationalFullResponseProgram.fixedQueueBound security order := by unfold _root_.CurrentAFT.RationalFullResponseProgram.fixedQueueBound; positivity
  have hE : 0 ≤ _root_.CurrentAFT.RationalFullResponseProgram.fixedQueueError security order := _p2mH89 _ _ _ _ _ hfB hb hfE he
  have hR : 0 ≤ _root_.CurrentAFT.RationalFullResponseProgram.responseError security order := add_nonneg hE hB
  exact ⟨hb, he, hB, hE, hR, add_nonneg hR (_p2mH151 security order)⟩
open _root_.P2Mb608f3c5 renaming h130 → _p2mH130
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h133 (security order : ℕ) (horder : 2 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.FullResponseWeightedIdentity.fixedQueue security order horder hroom queue source layout)
      arity colors centers| ≤ _root_.CurrentAFT.RationalFullResponseProgram.fixedQueueBound security order := by
  change |_root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.GradedControlAlgebra.familyProduct (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
    (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder queue)
    (_root_.CurrentAFT.FullResponseWeightedIdentity.choiceAverage security order (by omega) hroom queue source layout)) arity colors centers| ≤ _
  rw [← _p2mH86]
  exact (_p2mH119 order _ _ _ _
    (_p2mH94 security order) (_p2mH130 security order).1
    (_p2mH93 security order horder queue)
    (choiceAverage_bound security order (by omega) hroom queue source layout) arity colors centers).trans_eq
      (by unfold _root_.CurrentAFT.RationalFullResponseProgram.fixedQueueBound; ring)
open _root_.P2Mb608f3c5 renaming h133 → _p2mH133
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h134 (security bits order : ℕ) (horder : 2 ≤ order)
    (hroom : 2*order ≤ security) (hbody : order ≤ _root_.CurrentAFT.Parameters.bodySize security) (queue : ℤ)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (hfirst : _root_.CurrentAFT.RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(_root_.CurrentAFT.Parameters.base security:ℝ)))
    (hbudget : 64*(_root_.CurrentAFT.Parameters.base security:ℝ)*_root_.CurrentAFT.Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(_root_.CurrentAFT.Parameters.modulus security:ℝ)))
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (_root_.CurrentAFT.RationalFullResponseProgram.fixedQueue security bits order source.1.val.1.val source.1.val.2.val queue
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val)) arity colors centers-
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.FullResponseWeightedIdentity.fixedQueue security order horder hroom queue source layout)
        arity colors centers| ≤ _root_.CurrentAFT.RationalFullResponseProgram.fixedQueueError security order*(1/(2:ℝ)^bits) := by
  exact _p2mH90 security bits order (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder queue)
    (_root_.CurrentAFT.FullResponseWeightedIdentity.choiceAverage security order (by omega) hroom queue source layout)
    (_root_.CurrentAFT.RationalBackgroundPopulationProgram.current security bits order queue)
    (_root_.CurrentAFT.RationalFullResponseProgram.choiceAverage security bits order source.1.val.1.val source.1.val.2.val queue
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val))
    _ _ _ _ (_p2mH94 security order) (_p2mH130 security order).1
    (_p2mH96 security order) (_p2mH130 security order).2.1
    (_p2mH93 security order horder queue)
    (choiceAverage_bound security order (by omega) hroom queue source layout)
    (RationalBackgroundPopulationProgram.current_error security bits order horder queue hfirst hprecision hbudget)
    (_p2mH129 security bits order (by omega) hroom hbody queue source layout hfirst hprecision hbudget)
    arity colors centers
open _root_.P2Mb608f3c5 renaming h134 → _p2mH134
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h136 (security bits order : ℕ) (horder : 2 ≤ order)
    (hroom : 2*order ≤ security) (hbody : order ≤ _root_.CurrentAFT.Parameters.bodySize security)
    (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (hfirst : _root_.CurrentAFT.RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(_root_.CurrentAFT.Parameters.base security:ℝ)))
    (hbudget : 64*(_root_.CurrentAFT.Parameters.base security:ℝ)*_root_.CurrentAFT.Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(_root_.CurrentAFT.Parameters.modulus security:ℝ)))
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (_root_.CurrentAFT.RationalFullResponseProgram.response security bits order source.1.val.1.val source.1.val.2.val
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val)) arity colors centers-
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (_root_.CurrentAFT.FullResponseWeightedIdentity.response security order horder hroom source layout)
        arity colors centers| ≤ _root_.CurrentAFT.RationalFullResponseProgram.responseError security order*(1/(2:ℝ)^bits) := by
  exact _p2mH190 security bits order
    (fun scalar => _root_.CurrentAFT.FullResponseWeightedIdentity.fixedQueue security order horder hroom scalar.val source layout)
    (fun queue => _root_.CurrentAFT.RationalFullResponseProgram.fixedQueue security bits order source.1.val.1.val source.1.val.2.val queue
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val))
    _ _ (_p2mH130 security order).2.2.1
    (fun scalar => _p2mH133 security order horder hroom scalar.val source layout)
    (fun scalar => _p2mH134 security bits order horder hroom hbody scalar.val source layout hfirst hprecision hbudget)
    arity colors centers
open _root_.P2Mb608f3c5 renaming h136 → _p2mH136
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h125 (security bits order : ℕ) (source : _root_.CurrentAFT.FullResponsePointFormula.Index security order)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(_root_.CurrentAFT.Parameters.base security:ℝ)))
    (hbudget : 64*(_root_.CurrentAFT.Parameters.base security:ℝ)*_root_.CurrentAFT.Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(_root_.CurrentAFT.Parameters.modulus security:ℝ)))
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (colors : Fin arity.val.1.val → _root_.CurrentAFT.FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → _root_.CurrentAFT.ActualControls.SafePalette security) :
    |_root_.CurrentAFT.RationalActualFamilyApproximation.interpret security order (_root_.CurrentAFT.RationalFullResponseProgram.basis security bits order source.1
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val)) arity colors centers-
      _root_.CurrentAFT.RationalActualFamilyApproximation.data security order (Pi.single source.1 (_root_.CurrentAFT.FullResponseWeightedIdentity.sourceKernel security order source))
        arity colors centers| ≤ _root_.CurrentAFT.RationalPackedRootProgram.kernelErrorBound security order*(1/(2:ℝ)^bits) := by
  by_cases he : arity=source.1
  · subst arity
    simp only [_root_.CurrentAFT.RationalActualFamilyApproximation.interpret, _root_.CurrentAFT.RationalFamilyProductProgram.pullback, _root_.CurrentAFT.RationalFamilyProductProgram.realTable,
      _root_.CurrentAFT.RationalFullResponseProgram.basis, Fin.cast_refl, _root_.CurrentAFT.RationalActualFamilyApproximation.data, Pi.single_eq_same, _root_.CurrentAFT.FullResponseWeightedIdentity.sourceKernel]
    exact (_p2mH205 security bits _ _ source.2.1 source.2.2 hprecision hbudget colors centers).trans
      (mul_le_mul_of_nonneg_right (_p2mH153 security order _ _ source.1.property) (by positivity))
  · simp only [_root_.CurrentAFT.RationalActualFamilyApproximation.interpret, _root_.CurrentAFT.RationalFamilyProductProgram.pullback, _root_.CurrentAFT.RationalFamilyProductProgram.realTable,
      _root_.CurrentAFT.RationalFullResponseProgram.basis, dif_neg he, _root_.CurrentAFT.RationalActualFamilyApproximation.data, Pi.single_eq_of_ne he, Submodule.coe_zero, Pi.zero_apply, Rat.cast_zero, sub_zero, abs_zero]
    exact mul_nonneg (_p2mH151 security order) (by positivity)
open _root_.P2Mb608f3c5 renaming h125 → _p2mH125
end
open _root_.P2Mb608f3c5 renaming h125 → _p2mH125
open _root_.P2Mb608f3c5 renaming h130 → _p2mH130
open _root_.P2Mb608f3c5 renaming h133 → _p2mH133
open _root_.P2Mb608f3c5 renaming h134 → _p2mH134
open _root_.P2Mb608f3c5 renaming h136 → _p2mH136
end CurrentAFT.RationalFullResponseProgram
open _root_.P2Mb608f3c5 renaming h125 → _p2mH125
open _root_.P2Mb608f3c5 renaming h130 → _p2mH130
open _root_.P2Mb608f3c5 renaming h133 → _p2mH133
open _root_.P2Mb608f3c5 renaming h134 → _p2mH134
open _root_.P2Mb608f3c5 renaming h136 → _p2mH136
end
open _root_.P2Mb608f3c5 renaming h125 → _p2mH125
open _root_.P2Mb608f3c5 renaming h130 → _p2mH130
open _root_.P2Mb608f3c5 renaming h133 → _p2mH133
open _root_.P2Mb608f3c5 renaming h134 → _p2mH134
open _root_.P2Mb608f3c5 renaming h136 → _p2mH136
namespace CurrentAFT.FullResponseWeightedIdentity.response
end CurrentAFT.FullResponseWeightedIdentity.response
namespace CurrentAFT.RationalFullResponseProgram.errorConstant
end CurrentAFT.RationalFullResponseProgram.errorConstant
namespace CurrentAFT.RationalFullResponseProgram.fixedQueueBound
end CurrentAFT.RationalFullResponseProgram.fixedQueueBound
namespace CurrentAFT.RationalFullResponseProgram.fixedQueueError
end CurrentAFT.RationalFullResponseProgram.fixedQueueError
namespace CurrentAFT.RationalFullResponseProgram.responseError
end CurrentAFT.RationalFullResponseProgram.responseError
namespace CurrentAFT.RationalFullResponseProgram.rootBound
end CurrentAFT.RationalFullResponseProgram.rootBound
namespace CurrentAFT.RationalFullResponseProgram.rootError
end CurrentAFT.RationalFullResponseProgram.rootError
namespace CurrentAFT.RationalFullResponseProgram.tagCountBound
end CurrentAFT.RationalFullResponseProgram.tagCountBound
section
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock GradedControlAlgebra ActualControls FullResponsePointFormula RationalActualFamilyApproximation
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalFullResponseProgram.matrixFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  ProposalPrimary.primaryLaw bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h135 (security bits order : ℕ) (horder : 2 ≤ order)
    (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security)
    (hbody : order ≤ _root_.CurrentAFT.Parameters.bodySize security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (hfirst : _root_.CurrentAFT.RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(_root_.CurrentAFT.Parameters.base security:ℝ)))
    (hbudget : 64*(_root_.CurrentAFT.Parameters.base security:ℝ)*_root_.CurrentAFT.Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(_root_.CurrentAFT.Parameters.modulus security:ℝ)))
    (output source : _root_.CurrentAFT.FullResponsePointFormula.Index security order) :
    |(_root_.CurrentAFT.RationalFullResponseProgram.matrix security bits order output source:ℝ)-
      LinearMap.toMatrix' (_root_.CurrentAFT.CalibrationTableNorm.exactDefect security order horder hsecurity layout) output source| ≤
      _root_.CurrentAFT.RationalFullResponseProgram.errorConstant security order*(1/(2:ℝ)^bits) := by
  let room := _root_.CurrentAFT.ActualCompleteStability.room security order horder hsecurity
  have hr := _p2mH136 security bits order horder room hbody source layout hfirst hprecision hbudget
    output.1 output.2.1 output.2.2
  have hb := _p2mH125 security bits order source hprecision hbudget output.1 output.2.1 output.2.2
  rw [_p2mH60]
  simp only [_root_.CurrentAFT.RationalFullResponseProgram.matrix, _root_.CurrentAFT.RationalFullResponseProgram.defect, Pi.sub_apply, Rat.cast_sub]
  simp only [_root_.CurrentAFT.RationalActualFamilyApproximation.interpret, _root_.CurrentAFT.RationalFamilyProductProgram.pullback, _root_.CurrentAFT.RationalFamilyProductProgram.realTable, Function.comp_def] at hr hb
  simp only [_root_.CurrentAFT.RationalActualFamilyApproximation.data, Pi.single, Function.update] at hr hb ⊢
  have h := (abs_sub _ _).trans (add_le_add hr hb)
  convert h using 1 <;> first | rfl | (unfold _root_.CurrentAFT.RationalFullResponseProgram.errorConstant; ring) | (congr 1 <;> ring)
open _root_.P2Mb608f3c5 renaming h135 → _p2mH135
end
open _root_.P2Mb608f3c5 renaming h135 → _p2mH135
end CurrentAFT.RationalFullResponseProgram
open _root_.P2Mb608f3c5 renaming h135 → _p2mH135
end
open _root_.P2Mb608f3c5 renaming h135 → _p2mH135
namespace CurrentAFT.BinaryCalibrationWeightSemantic
end CurrentAFT.BinaryCalibrationWeightSemantic
namespace CurrentAFT.BinaryRectangleMaterialization
end CurrentAFT.BinaryRectangleMaterialization
namespace CurrentAFT.BinaryRectangleMaterialization.Dimensions
end CurrentAFT.BinaryRectangleMaterialization.Dimensions
namespace CurrentAFT.BinaryRectangleMaterialization.Dimensions.mk
end CurrentAFT.BinaryRectangleMaterialization.Dimensions.mk
namespace CurrentAFT.BinaryRectangleMaterialization.Result
end CurrentAFT.BinaryRectangleMaterialization.Result
namespace CurrentAFT.BinaryRectangleMaterialization.Result.mk
end CurrentAFT.BinaryRectangleMaterialization.Result.mk
namespace CurrentAFT.BinaryRectangleMaterialization.current
end CurrentAFT.BinaryRectangleMaterialization.current
namespace CurrentAFT.BinaryRectangleMaterialization.dimensions
end CurrentAFT.BinaryRectangleMaterialization.dimensions
namespace CurrentAFT.BinaryRectangleMaterialization.rhsEntry
end CurrentAFT.BinaryRectangleMaterialization.rhsEntry
namespace CurrentAFT.BinaryRectangleMaterialization.scalarPoint
end CurrentAFT.BinaryRectangleMaterialization.scalarPoint
namespace CurrentAFT.CurrentRectangleIndex
end CurrentAFT.CurrentRectangleIndex
namespace CurrentAFT.CurrentRectangleIndex.colors
end CurrentAFT.CurrentRectangleIndex.colors
namespace CurrentAFT.CurrentRectangleIndex.pointEquiv
end CurrentAFT.CurrentRectangleIndex.pointEquiv
namespace CurrentAFT.RationalFullResponseProgram.matrix
end CurrentAFT.RationalFullResponseProgram.matrix
section
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock GradedControlAlgebra ActualControls FullResponsePointFormula
  CalibrationPrecisionRates CalibratedWeightApproximation CalibrationTableNorm
open Filter
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalFullResponseProgram.accuracyFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  ProposalPrimary.primaryLaw bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h131 (order : ℕ) : 0 ≤ _root_.CurrentAFT.RationalFullResponseProgram.entryConstant order ∧
    ∀ security, |_root_.CurrentAFT.RationalFullResponseProgram.errorConstant security order| ≤ _root_.CurrentAFT.RationalFullResponseProgram.entryConstant order*(_root_.CurrentAFT.Parameters.base security:ℝ)^(_root_.CurrentAFT.RationalFullResponseProgram.entryDegree order) :=
  Classical.choose_spec (Classical.choose_spec (_root_.CurrentAFT.RationalFullResponseProgram.error_polynomial order))
open _root_.P2Mb608f3c5 renaming h131 → _p2mH131
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h132 (security order : ℕ) :
    _root_.CurrentAFT.RationalFullResponseProgram.errorConstant security order*(1/(2:ℝ)^security) ≤ _root_.CurrentAFT.RationalFullResponseProgram.entryError security order := by
  have h := mul_le_mul_of_nonneg_right ((le_abs_self _).trans ((_p2mH131 order).2 security))
    (by positivity : (0:ℝ) ≤ 1/2^security)
  simpa only [_root_.CurrentAFT.RationalFullResponseProgram.entryError, _root_.CurrentAFT.CalibrationPrecisionRates.entryBudget, div_pow, one_pow] using h
open _root_.P2Mb608f3c5 renaming h132 → _p2mH132
set_option maxRecDepth 8192
theorem _root_.P2Mb608f3c5.h126 (security order : ℕ) (hroom : 2*order ≤ security) : order ≤ _root_.CurrentAFT.Parameters.bodySize security := by
  have hb : security ≤ _root_.CurrentAFT.Parameters.base security := by unfold _root_.CurrentAFT.Parameters.base; omega
  have hb1 : 1 ≤ _root_.CurrentAFT.Parameters.base security := (_root_.CurrentAFT.Parameters.base_ge_two security).trans' (by omega)
  have hp : _root_.CurrentAFT.Parameters.base security ≤ _root_.CurrentAFT.Parameters.base security^96 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (by omega : 1 ≤ 96)
  have hq : 1 ≤ _root_.CurrentAFT.Parameters.modulus security := (_root_.CurrentAFT.Parameters.modulus_spec security).2.one_le
  rw [_root_.CurrentAFT.Parameters.bodySize_eq]
  exact (show order ≤ security by omega).trans (hb.trans (hp.trans (by simpa using Nat.mul_le_mul_right (_root_.CurrentAFT.Parameters.base security^96) hq)))
open _root_.P2Mb608f3c5 renaming h126 → CurrentAFT.RationalFullResponseProgram.body_room
open _root_.P2Mb608f3c5 renaming h126 → _p2mH126
set_option maxRecDepth 8192
theorem _root_.CurrentAFT.RationalFullResponseProgram.__p2m_proof_b608f3c5e9ae64504cc2 (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      ∀ hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security,
      ∀ (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) (output source : _root_.CurrentAFT.FullResponsePointFormula.Index security order),
        |(_root_.CurrentAFT.RationalFullResponseProgram.matrix security security order output source:ℝ)-
          LinearMap.toMatrix' (_root_.CurrentAFT.CalibrationTableNorm.exactDefect security order horder hsecurity layout) output source| ≤ _root_.CurrentAFT.RationalFullResponseProgram.entryError security order := by
  filter_upwards [_p2mH69] with security hb hsecurity layout output source
  exact (_p2mH135 security security order horder hsecurity
    (_p2mH126 security order (_root_.CurrentAFT.ActualCompleteStability.room security order horder hsecurity)) layout
    hb.2.2 hb.1 hb.2.1 output source).trans (_p2mH132 security order)
end
open _root_.P2Mb608f3c5 renaming h126 → CurrentAFT.RationalFullResponseProgram.body_room
open _root_.P2Mb608f3c5 renaming h126 → _p2mH126
open _root_.P2Mb608f3c5 renaming h131 → _p2mH131
open _root_.P2Mb608f3c5 renaming h132 → _p2mH132
end CurrentAFT.RationalFullResponseProgram
open _root_.P2Mb608f3c5 renaming h126 → CurrentAFT.RationalFullResponseProgram.body_room
open _root_.P2Mb608f3c5 renaming h126 → _p2mH126
open _root_.P2Mb608f3c5 renaming h131 → _p2mH131
open _root_.P2Mb608f3c5 renaming h132 → _p2mH132
end
open _root_.P2Mb608f3c5 renaming h126 → CurrentAFT.RationalFullResponseProgram.body_room
open _root_.P2Mb608f3c5 renaming h126 → _p2mH126
open _root_.P2Mb608f3c5 renaming h131 → _p2mH131
open _root_.P2Mb608f3c5 renaming h132 → _p2mH132
set_option maxRecDepth 65536
theorem solution : (type_of% @_root_.CurrentAFT.RationalFullResponseProgram.__p2m_proof_b608f3c5e9ae64504cc2) := @_root_.CurrentAFT.RationalFullResponseProgram.__p2m_proof_b608f3c5e9ae64504cc2
