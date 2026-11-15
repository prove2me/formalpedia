-- Prove2me | solution 1 for CurrentAFT.RationalPackedRootProgram.current_error_raw
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T20:20:34.214267+00:00
-- url     : https://prove2.me/submissions/06394a73-0437-4ae8-8580-bb63f5c1f758

import Definitions.Def_InfoLossLAR_NativeBundle_12
import Theorems.Thm_AFT_FiniteDist_l1_independent_le
import Theorems.Thm_AFT_FiniteDist_l1_prod_le
namespace P2M9e1cfc64
end P2M9e1cfc64
section
namespace AFT.RationalNumerics
open scoped BigOperators
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h4 (value : ℝ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (index : ℕ) :
    |(-1 : ℝ)^index*value^(2*index+1)/(2*index+1 : ℕ)| ≤ (1/2 : ℝ)^(index+1) := by
  rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (pow_nonneg hv _),abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ value^(2*index+1) := div_le_self (pow_nonneg hv _) (by exact_mod_cast (show 1≤2*index+1 by omega))
    _ ≤ (1/2 : ℝ)^(2*index+1) := pow_le_pow_left₀ hv hv' _
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
open _root_.P2M9e1cfc64 renaming h4 → _p2mH4
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h3 (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (terms : ℕ) :
    |(arctanSum value terms : ℝ)-Real.arctan value| ≤ (1/2 : ℝ)^terms := by
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
  have hcast : (arctanSum value terms : ℝ)=∑ i∈Finset.range terms,term i := by
    unfold arctanSum term
    push_cast
    rfl
  have hgeom : Summable (fun i : ℕ => (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i) :=
    (summable_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left _
  have hbound (i : ℕ) : ‖term (i+terms)‖ ≤ (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i := by
    have hh := _p2mH4 (value : ℝ) hv0 hv1 (i+terms)
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
open _root_.P2M9e1cfc64 renaming h3 → _p2mH3
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h12 (bits : ℕ) : |(piApprox bits : ℝ)-Real.pi| ≤ 1/(2 : ℝ)^bits := by
  have h1 := _p2mH3 (1/2) (by norm_num) (by norm_num) (bits+3)
  have h2 := _p2mH3 (1/3) (by norm_num) (by norm_num) (bits+3)
  have hid : Real.pi=4*(Real.arctan (1/2)+Real.arctan (1/3)) := by
    have hh := Real.arctan_inv_2_add_arctan_inv_3
    norm_num only [one_div] at ⊢
    linarith
  have he : (piApprox bits : ℝ)-Real.pi=4*((arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)+
      ((arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3))) := by
    rw [hid]
    simp only [piApprox,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add]
    ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    _ ≤ 4*(|(arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)|+
        |(arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3)|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ 4*((1/2 : ℝ)^(bits+3)+(1/2 : ℝ)^(bits+3)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using add_le_add h1 h2
    _ = _ := by rw [pow_add,div_pow,one_pow]; norm_num; ring
open _root_.P2M9e1cfc64 renaming h12 → _p2mH12
end
open _root_.P2M9e1cfc64 renaming h3 → _p2mH3
open _root_.P2M9e1cfc64 renaming h4 → _p2mH4
open _root_.P2M9e1cfc64 renaming h12 → _p2mH12
end AFT.RationalNumerics
open _root_.P2M9e1cfc64 renaming h3 → _p2mH3
open _root_.P2M9e1cfc64 renaming h4 → _p2mH4
open _root_.P2M9e1cfc64 renaming h12 → _p2mH12
end
open _root_.P2M9e1cfc64 renaming h4 → _p2mH4
open _root_.P2M9e1cfc64 renaming h12 → _p2mH12
open _root_.P2M9e1cfc64 renaming h3 → _p2mH3
section
namespace AFT.RationalNumerics
open scoped BigOperators
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h7 (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2)
    (terms : ℕ) (ht : 0 < terms) :
    |(expSum value terms : ℝ)-Real.exp value| ≤ 2*(1/2 : ℝ)^terms := by
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
  have he : (expSum value terms : ℝ)=∑ i∈Finset.range terms,(value : ℝ)^i/(i.factorial : ℕ) := by
    unfold expSum
    push_cast
    rfl
  rw [he,abs_sub_comm]
  apply hh.trans
  rw [abs_of_nonneg hv0]
  exact (mul_le_mul (pow_le_pow_left₀ hv0 hv1 terms) hquot (by positivity) (by positivity)).trans_eq (mul_comm _ _)
open _root_.P2M9e1cfc64 renaming h7 → _p2mH7
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h11 (first second : ℝ) (hf : 1 ≤ first) (hs : 1 ≤ second) :
    |first⁻¹-second⁻¹| ≤ |first-second| := by
  have hfirst : first ≠ 0 := by linarith
  have hsecond : second ≠ 0 := by linarith
  have he : first⁻¹-second⁻¹=(second-first)/(first*second) := by field_simp
  rw [he,abs_div,abs_sub_comm,abs_of_nonneg (by positivity : 0 ≤ first*second)]
  exact div_le_self (abs_nonneg _) (by nlinarith)
open _root_.P2M9e1cfc64 renaming h11 → _p2mH11
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h13 (first second : ℝ)
    (hf : 0 ≤ first ∧ first ≤ 1) (hs : 0 ≤ second ∧ second ≤ 1) (count : ℕ) :
    |first^count-second^count| ≤ (count : ℝ)*|first-second| := by
  have hh := abs_pow_sub_pow_le first second count
  rw [abs_of_nonneg hf.1,abs_of_nonneg hs.1] at hh
  have hp : max first second^(count-1) ≤ 1 := pow_le_one₀ (le_max_of_le_left hf.1) (max_le hf.2 hs.2)
  calc
    _ ≤ |first-second| *count*max first second^(count-1) := hh
    _ ≤ |first-second| *count*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring
open _root_.P2M9e1cfc64 renaming h13 → _p2mH13
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h6 (argument : ℚ) (scale bits : ℕ)
    (ha : 0 ≤ argument) (hscale : 0 < scale) (hbound : 2*argument ≤ (scale : ℚ)) :
    |(expNegScaled argument scale bits : ℝ)-Real.exp (-(argument : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let value : ℚ := argument/(scale : ℚ)
  let terms := bits+scale+1
  have hs0 : (0 : ℚ) < scale := by exact_mod_cast hscale
  have hv0 : 0 ≤ value := div_nonneg ha hs0.le
  have hv1 : value ≤ 1/2 := by
    apply (div_le_iff₀ hs0).mpr
    linarith
  have ht : 0 < terms := by dsimp [terms]; omega
  have hfirst := expSum_ge_one value hv0 terms ht
  have hsecond : (1 : ℝ) ≤ Real.exp (value : ℝ) := Real.one_le_exp_iff.mpr (by exact_mod_cast hv0)
  have hpi := _p2mH13 ((expSum value terms : ℝ)⁻¹) ((Real.exp (value : ℝ))⁻¹)
    ⟨by positivity,inv_le_one_of_one_le₀ hfirst⟩ ⟨by positivity,inv_le_one_of_one_le₀ hsecond⟩ scale
  have hi := _p2mH11 (expSum value terms) (Real.exp (value : ℝ)) hfirst hsecond
  have happrox := (hpi.trans (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg scale))).trans
    (mul_le_mul_of_nonneg_left (_p2mH7 value hv0 hv1 terms ht) (Nat.cast_nonneg scale))
  have hexp : (Real.exp (value : ℝ))⁻¹^scale=Real.exp (-(argument : ℝ)) := by
    rw [← Real.exp_neg,← Real.exp_nat_mul]
    congr 1
    dsimp [value]
    push_cast
    field_simp
  have hprogram : (expNegScaled argument scale bits : ℝ)=(expSum value terms : ℝ)⁻¹^scale := by
    simp only [expNegScaled,value,terms,Rat.cast_pow,Rat.cast_inv]
  rw [hprogram,← hexp]
  apply happrox.trans
  have hsbound : (scale : ℝ) ≤ (2 : ℝ)^scale := by exact_mod_cast (Nat.lt_two_pow_self (n:=scale)).le
  calc
    _ ≤ (2 : ℝ)^scale*(2*(1/2 : ℝ)^terms) := mul_le_mul_of_nonneg_right hsbound (by positivity)
    _ = _ := by
      dsimp [terms]
      rw [pow_add,pow_add,div_pow,one_pow,div_pow,one_pow]
      field_simp
open _root_.P2M9e1cfc64 renaming h6 → _p2mH6
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h5 (argument : ℚ) (bits : ℕ) :
    |(expNegApprox argument bits : ℝ)-Real.exp (-max (argument : ℝ) 0)| ≤ 1/(2 : ℝ)^bits := by
  have hb : 2*max argument 0 ≤ (expScale argument : ℚ) := by
    have hh := Nat.le_ceil (max argument 0)
    simp only [expScale,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    linarith
  have hh := _p2mH6 (max argument 0) (expScale argument) bits
    (le_max_right _ _) (expScale_positive argument) hb
  simpa only [expNegApprox,Rat.cast_max,Rat.cast_zero] using hh
open _root_.P2M9e1cfc64 renaming h5 → _p2mH5
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h8 (first second : ℝ) (hf : 0 ≤ first) (hs : 0 ≤ second) :
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
open _root_.P2M9e1cfc64 renaming h8 → _p2mH8
end
open _root_.P2M9e1cfc64 renaming h5 → _p2mH5
open _root_.P2M9e1cfc64 renaming h6 → _p2mH6
open _root_.P2M9e1cfc64 renaming h7 → _p2mH7
open _root_.P2M9e1cfc64 renaming h8 → _p2mH8
open _root_.P2M9e1cfc64 renaming h11 → _p2mH11
open _root_.P2M9e1cfc64 renaming h13 → _p2mH13
end AFT.RationalNumerics
open _root_.P2M9e1cfc64 renaming h5 → _p2mH5
open _root_.P2M9e1cfc64 renaming h6 → _p2mH6
open _root_.P2M9e1cfc64 renaming h7 → _p2mH7
open _root_.P2M9e1cfc64 renaming h8 → _p2mH8
open _root_.P2M9e1cfc64 renaming h11 → _p2mH11
open _root_.P2M9e1cfc64 renaming h13 → _p2mH13
end
open _root_.P2M9e1cfc64 renaming h8 → _p2mH8
open _root_.P2M9e1cfc64 renaming h5 → _p2mH5
open _root_.P2M9e1cfc64 renaming h7 → _p2mH7
open _root_.P2M9e1cfc64 renaming h11 → _p2mH11
open _root_.P2M9e1cfc64 renaming h6 → _p2mH6
open _root_.P2M9e1cfc64 renaming h13 → _p2mH13
section
namespace AFT.RationalNumerics
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h9 (squaredWidth : ℚ) (point : ℤ) (bits : ℕ)
    (hwidth : 0 < squaredWidth) :
    |(gaussianApprox squaredWidth point bits : ℝ)-
      Real.exp (-Real.pi*(point : ℝ)^2/(squaredWidth : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let ratio := gaussianRatio squaredWidth point
  let guard := gaussianGuard squaredWidth point
  let argument := piApprox (bits+guard+1)*ratio
  have hr0 : (0 : ℚ) ≤ ratio := div_nonneg (sq_nonneg _) hwidth.le
  have hr : (0 : ℝ) ≤ ratio := by exact_mod_cast hr0
  have hguard : (ratio : ℝ) ≤ (guard : ℝ) := by exact_mod_cast Nat.le_ceil ratio
  have hguardpow : (guard : ℝ) ≤ (2 : ℝ)^guard := by exact_mod_cast (Nat.lt_two_pow_self (n:=guard)).le
  have hpi := _p2mH12 (bits+guard+1)
  have harg : |(argument : ℝ)-Real.pi*(ratio : ℝ)| ≤ 1/(2 : ℝ)^(bits+1) := by
    have he : (argument : ℝ)-Real.pi*(ratio : ℝ)=((piApprox (bits+guard+1) : ℝ)-Real.pi)*(ratio : ℝ) := by
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
  have he := _p2mH5 argument (bits+1)
  have hl := _p2mH8 (max (argument : ℝ) 0) (Real.pi*(ratio : ℝ)) (le_max_right _ _) ht
  have htarget : -Real.pi*(point : ℝ)^2/(squaredWidth : ℝ) = -(Real.pi*(ratio : ℝ)) := by
    dsimp [ratio,gaussianRatio]
    push_cast
    ring
  rw [htarget]
  calc
    _ ≤ |(expNegApprox argument (bits+1) : ℝ)-Real.exp (-max (argument : ℝ) 0)|+
        |Real.exp (-max (argument : ℝ) 0)-Real.exp (-(Real.pi*(ratio : ℝ)))| := abs_sub_le _ _ _
    _ ≤ 1/(2 : ℝ)^(bits+1)+1/(2 : ℝ)^(bits+1) := add_le_add he (hl.trans hclip)
    _ = _ := by rw [pow_succ]; field_simp; norm_num
open _root_.P2M9e1cfc64 renaming h9 → _p2mH9
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h10 (squaredWidth : ℚ) (width : ℝ) (point : ℤ) (bits : ℕ)
    (hwidth : 0 < squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) :
    |(gaussianApprox squaredWidth point bits : ℝ)-GaussianSource.weight width point| ≤ 1/(2 : ℝ)^bits := by
  convert _p2mH9 squaredWidth point bits hwidth using 1
  unfold GaussianSource.weight
  rw [hsquare]
  have h : -(Real.pi / (squaredWidth : ℝ)) * (point : ℝ)^2 =
      -Real.pi * (point : ℝ)^2 / (squaredWidth : ℝ) := by ring
  rw [h]
open _root_.P2M9e1cfc64 renaming h10 → _p2mH10
end
open _root_.P2M9e1cfc64 renaming h9 → _p2mH9
open _root_.P2M9e1cfc64 renaming h10 → _p2mH10
end AFT.RationalNumerics
open _root_.P2M9e1cfc64 renaming h9 → _p2mH9
open _root_.P2M9e1cfc64 renaming h10 → _p2mH10
end
open _root_.P2M9e1cfc64 renaming h9 → _p2mH9
open _root_.P2M9e1cfc64 renaming h10 → _p2mH10
section
namespace AFT.SignedConditioning
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h15 (first second : Color → ℝ) :
    |(∑ color, first color) - ∑ color, second color| ≤ ∑ color, |first color - second color| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _
open _root_.P2M9e1cfc64 renaming h15 → _p2mH15
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h16 (signed reference : Color → ℝ)
    (href : ∀ color, 0 ≤ reference color)
    (hsigned : 0 < ∑ color, signed color) (hreference : 0 < ∑ color, reference color) :
    (∑ color, |signed color / (∑ x, signed x) - reference color / (∑ x, reference x)|) ≤
      2 * (∑ color, |signed color - reference color|) / (∑ color, signed color) := by
  let total := ∑ color, signed color
  let referenceTotal := ∑ color, reference color
  let error := ∑ color, |signed color - reference color|
  have hmass : |referenceTotal - total| ≤ error := by
    simpa only [abs_sub_comm] using _p2mH15 signed reference
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
open _root_.P2M9e1cfc64 renaming h16 → _p2mH16
end
open _root_.P2M9e1cfc64 renaming h15 → _p2mH15
open _root_.P2M9e1cfc64 renaming h16 → _p2mH16
end AFT.SignedConditioning
open _root_.P2M9e1cfc64 renaming h15 → _p2mH15
open _root_.P2M9e1cfc64 renaming h16 → _p2mH16
end
open _root_.P2M9e1cfc64 renaming h15 → _p2mH15
open _root_.P2M9e1cfc64 renaming h16 → _p2mH16
section
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h14 (squaredWidth : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hwidth : 0 < squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) :
    (∑ point,|(windowApproxLaw squaredWidth cutoff bits).weight point-
      (windowGaussian width cutoff).weight point|) ≤ 1/(2 : ℝ)^bits := by
  let raw : Window cutoff → ℝ := fun point => (windowApproxRaw squaredWidth cutoff bits point : ℝ)
  have hraw : 1 ≤ ∑ point,raw point := by
    have hh := windowApproxNormalizer_ge_one squaredWidth cutoff bits
    rw [windowApproxNormalizer_eq_sum] at hh
    dsimp only [raw]
    exact_mod_cast hh
  have hnormal := _p2mH16 raw (fun point => GaussianSource.weight width point)
    (fun point => (weight_pos _ _).le) (zero_lt_one.trans_le hraw)
    (zero_lt_one.trans_le (windowNormalizer_ge_one width cutoff))
  have herr : (∑ point,|raw point-GaussianSource.weight width point|) ≤
      (2*cutoff+1 : ℕ)/(2 : ℝ)^(windowApproxPrecision cutoff bits) := by
    have hh := Finset.sum_le_sum (fun point (_ : point ∈ (Finset.univ : Finset (Window cutoff))) =>
      _p2mH10 squaredWidth width point (windowApproxPrecision cutoff bits) hwidth hsquare)
    have hc : Fintype.card (Window cutoff)=2*cutoff+1 := by
      rw [← Fintype.card_congr (windowIndexEquiv cutoff),Fintype.card_fin]
    simpa only [raw,windowApproxRaw,Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul,mul_one_div] using hh
  have hden : 0 ≤ ∑ point,|raw point-GaussianSource.weight width point| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have heq : (∑ point,|(windowApproxLaw squaredWidth cutoff bits).weight point-
      (windowGaussian width cutoff).weight point|)=
      ∑ point,|raw point/(∑ x,raw x)-GaussianSource.weight width point/(∑ x:Window cutoff,GaussianSource.weight width x)| := by
    apply Finset.sum_congr rfl
    intro point _
    simp only [windowApproxLaw,windowApproxWeight,windowApproxNormalizer_eq_sum,windowGaussian,FiniteDist.normalize,raw,Rat.cast_div,Rat.cast_sum]
  rw [heq]
  calc
    _ ≤ 2*(∑ point,|raw point-GaussianSource.weight width point|)/(∑ x,raw x) := hnormal
    _ ≤ 2*(∑ point,|raw point-GaussianSource.weight width point|)/1 :=
      div_le_div_of_nonneg_left (by positivity) zero_lt_one hraw
    _ ≤ 2*((2*cutoff+1 : ℕ)/(2 : ℝ)^(windowApproxPrecision cutoff bits)) := by rw [div_one]; gcongr
    _ ≤ 2*((2 : ℝ)^(2*cutoff+1)/(2 : ℝ)^(windowApproxPrecision cutoff bits)) := by
      gcongr
      exact_mod_cast (Nat.lt_two_pow_self (n:=2*cutoff+1)).le
    _ = _ := by
      unfold windowApproxPrecision
      rw [pow_add,pow_add]
      field_simp
      ring
open _root_.P2M9e1cfc64 renaming h14 → _p2mH14
end
open _root_.P2M9e1cfc64 renaming h14 → _p2mH14
end AFT.RationalNumerics
open _root_.P2M9e1cfc64 renaming h14 → _p2mH14
end
open _root_.P2M9e1cfc64 renaming h14 → _p2mH14
namespace AFT
end AFT
namespace AFT.finiteCorrection
end AFT.finiteCorrection
section
namespace AFT
open scoped BigOperators
section RankOne
variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
end RankOne
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h23 (ρ scalar : ℝ) (hsmall : |scalar| ≤ ρ / 2) :
    ρ / 2 ≤ ρ + scalar := by
  have := (abs_le.mp hsmall).1
  linarith
open _root_.P2M9e1cfc64 renaming h23 → _p2mH23
section ContinuousLocalInverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E]
end ContinuousLocalInverse
section BoundaryCollapse
variable {ι : Type*} [DecidableEq ι]
end BoundaryCollapse
section ConjugatedProjection
variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
end ConjugatedProjection
end AFT
open _root_.P2M9e1cfc64 renaming h23 → _p2mH23
end
open _root_.P2M9e1cfc64 renaming h23 → _p2mH23
section
namespace AFT
open scoped BigOperators
section FiniteProfiles
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
end FiniteProfiles
section SignProfile
variable {ι : Type*} [Fintype ι]
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h22 (activation : ℝ) (signProfile sign : ι → ℝ)
    (hsign : ∀ color, |sign color| ≤ 1)
    (hsmall : (∑ color, |signProfile color|) < activation) (profile : ι → ℝ) :
    (finitePrimaryRankEquiv activation signProfile sign hsign hsmall).symm profile =
      profile - ((activation + signFunctional sign signProfile)⁻¹ *
        signFunctional sign profile) • signProfile := by
  exact primaryRankInverse_apply activation signProfile (profileSignMap sign) profile
open _root_.P2M9e1cfc64 renaming h22 → _p2mH22
end SignProfile
open _root_.P2M9e1cfc64 renaming h22 → _p2mH22
end AFT
open _root_.P2M9e1cfc64 renaming h22 → _p2mH22
end
open _root_.P2M9e1cfc64 renaming h22 → _p2mH22
section
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h1 (equiv : Slot ≃ Pool)
    (reference : Pool → FiniteDist Color) (function : (Slot → Color) → ℝ) :
    (FiniteDist.independent reference).expectation (fun word => function (word ∘ equiv)) =
      (FiniteDist.independent (fun slot => reference (equiv slot))).expectation function := by
  have h := (HistogramNormalization.renameWord (Color := Color) equiv).symm.sum_comp
    (fun word => (∏ slot, (reference (equiv slot)).weight (word slot)) * function word)
  unfold FiniteDist.expectation FiniteDist.independent
  apply Eq.trans ?_ h
  apply Finset.sum_congr (by ext; simp)
  intro word _
  change (∏ slot, (reference slot).weight (word slot)) * function (word ∘ equiv) =
    (∏ slot, (reference (equiv slot)).weight ((word ∘ equiv) slot)) * function (word ∘ equiv)
  congr 1
  exact (equiv.prod_comp (fun slot => (reference slot).weight (word slot))).symm
open _root_.P2M9e1cfc64 renaming h1 → _p2mH1
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h0 (reference : Pool → FiniteDist Color)
    (placement : Slot ↪ Pool) (function : (Slot → Color) → ℝ) :
    (FiniteDist.independent reference).expectation (fun word => function (word ∘ placement)) =
      (FiniteDist.independent (fun slot => reference (placement slot))).expectation function := by
  have hr := LocalTensors.independent_restriction_expectation reference (Finset.univ.map placement)
    (fun word => function (word ∘ placementEquiv placement))
  have he := _p2mH1 (placementEquiv placement)
    (fun label : Finset.univ.map placement => reference label) function
  apply Eq.trans ?_ (hr.trans ?_)
  · rfl
  · apply Eq.trans ?_ he
    unfold FiniteDist.expectation FiniteDist.independent
    apply Finset.sum_congr (by ext; simp)
    intro word _
    rfl
open _root_.P2M9e1cfc64 renaming h0 → _p2mH0
end AFT.CanonicalMoments
open _root_.P2M9e1cfc64 renaming h0 → _p2mH0
open _root_.P2M9e1cfc64 renaming h1 → _p2mH1
end
open _root_.P2M9e1cfc64 renaming h0 → _p2mH0
open _root_.P2M9e1cfc64 renaming h1 → _p2mH1
section
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators
noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h20 (start : ℤ) (width : ℕ) (point : ℤ) :
    |(intervalProbabilityProgram start width point : ℝ)|≤1 := by
  rw [intervalProbabilityProgram_cast,abs_of_nonneg (intervalAnchorLaw_nonneg _ _ _)]
  apply (intervalAnchorLaw_bound _ _ _).trans
  by_cases hw : width=0
  · subst width; norm_num
  have hh : (1 : ℝ)≤width := by exact_mod_cast (show 1≤width by omega)
  exact inv_le_one_of_one_le₀ hh
open _root_.P2M9e1cfc64 renaming h20 → _p2mH20
end
open _root_.P2M9e1cfc64 renaming h20 → _p2mH20
end AFT.V7Calibration
open _root_.P2M9e1cfc64 renaming h20 → _p2mH20
end
open _root_.P2M9e1cfc64 renaming h20 → _p2mH20
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualPairSourceApproxLaw
end AFT.V7Calibration.actualPairSourceApproxLaw
namespace AFT.V7Calibration.actualPairSourceProgram
end AFT.V7Calibration.actualPairSourceProgram
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
theorem _root_.P2M9e1cfc64.h21 (modulus boundary shift color : ℤ) :
    |(sliceProbabilityProgram modulus boundary shift color : ℝ)|≤1 := by
  rw [sliceProbabilityProgram_eq_original]
  split_ifs with hh
  · simp only [Rat.cast_inv,Rat.cast_natCast]
    rw [abs_of_nonneg (by positivity)]
    apply inv_le_one_of_one_le₀
    exact_mod_cast (Finset.one_le_card.mpr ⟨color,hh⟩)
  · norm_num
open _root_.P2M9e1cfc64 renaming h21 → _p2mH21
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h19 (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    |(averagedSliceProgram modulus boundary start source width color : ℝ)|≤1 := by
  by_cases hw : width=0
  · subst width
    simp [averagedSliceProgram_eq_sum,anchorInterval]
  simp only [averagedSliceProgram_eq_sum,Rat.cast_sum,Rat.cast_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ shift∈anchorInterval start width,intervalAnchorLaw start width shift := by
      apply Finset.sum_le_sum
      intro shift _
      rw [abs_mul,intervalProbabilityProgram_cast,abs_of_nonneg (intervalAnchorLaw_nonneg _ _ _)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (_p2mH21 modulus boundary (shift-source) color)
        (intervalAnchorLaw_nonneg start shift width)
    _ = 1 := intervalAnchorLaw_mass start width hw
open _root_.P2M9e1cfc64 renaming h19 → _p2mH19
end
open _root_.P2M9e1cfc64 renaming h19 → _p2mH19
open _root_.P2M9e1cfc64 renaming h21 → _p2mH21
end AFT.V7Calibration
open _root_.P2M9e1cfc64 renaming h19 → _p2mH19
open _root_.P2M9e1cfc64 renaming h21 → _p2mH21
end
open _root_.P2M9e1cfc64 renaming h21 → _p2mH21
open _root_.P2M9e1cfc64 renaming h19 → _p2mH19
section
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators
noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local instance] _root_.AFT.V7Calibration.conditionalPairProgramFinDecEq
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h18 (modulus : ℕ) (boundary start source : ℤ) (width : ℕ)
    (first second : Fin modulus) :
    (averagedPairProgram modulus boundary start source width first.val second.val : ℝ)=
      TrimmedSlice.averagedPair modulus boundary start source width first second := by
  simp only [averagedPairProgram,Rat.cast_mul,intervalProbabilityProgram_cast,sliceProbabilityProgram_cast,
    TrimmedSlice.averagedPair_formula]
open _root_.P2M9e1cfc64 renaming h18 → _p2mH18
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h17 (modulus : ℕ) (boundary start source : ℤ) (width first second : ℕ) :
    |(averagedPairProgram modulus boundary start source width first second : ℝ)| ≤ 1 := by
  simp only [averagedPairProgram,Rat.cast_mul,abs_mul]
  exact (mul_le_mul (_p2mH20 _ _ _) (_p2mH21 _ _ _ _)
    (abs_nonneg _) (by norm_num)).trans_eq (mul_one _)
open _root_.P2M9e1cfc64 renaming h17 → _p2mH17
end
open _root_.P2M9e1cfc64 renaming h17 → _p2mH17
open _root_.P2M9e1cfc64 renaming h18 → _p2mH18
end AFT.V7Calibration
open _root_.P2M9e1cfc64 renaming h17 → _p2mH17
open _root_.P2M9e1cfc64 renaming h18 → _p2mH18
end
open _root_.P2M9e1cfc64 renaming h17 → _p2mH17
open _root_.P2M9e1cfc64 renaming h18 → _p2mH18
section
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {Source State : Type*} [Fintype Source] [Fintype State]
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h2 (source : FiniteDist Source) (kernel : Source → ℝ) (bound : ℝ)
    (hkernel : ∀ point, |kernel point| ≤ bound) :
    |∑ point, source.weight point * kernel point| ≤ bound := by
  calc
    _ ≤ ∑ point, |source.weight point * kernel point| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ point, source.weight point * bound := by
      apply Finset.sum_le_sum
      intro point _
      rw [abs_mul,abs_of_nonneg (source.nonneg point)]
      exact mul_le_mul_of_nonneg_left (hkernel point) (source.nonneg point)
    _ = _ := by rw [← Finset.sum_mul,source.sum_one,one_mul]
open _root_.P2M9e1cfc64 renaming h2 → _p2mH2
end
open _root_.P2M9e1cfc64 renaming h2 → _p2mH2
end AFT.FiniteDist
open _root_.P2M9e1cfc64 renaming h2 → _p2mH2
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Source Slot Color : Type*} [Fintype Source] [Fintype Slot] [Fintype Color] [DecidableEq Slot]
end
end AFT.MixedKernel
end
open _root_.P2M9e1cfc64 renaming h2 → _p2mH2
section
namespace CurrentAFT.FirstResponse
open AFT DiffuseProfiles
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.sourceCutoff DiffuseProfiles.actualProfile DiffuseProfiles.signProfile
  DiffuseProfiles.activation DiffuseProfiles.actualSeedLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h84 (security : ℕ) :
    activation security / 2 ≤ activation security +
      signFunctional (anchorSign security) (signProfile security) :=
  _p2mH23 _ _
    ((signFunctional_abs_le_l1 (anchorSign security) (signProfile security)
      (anchorSign_abs_le_one security)).trans (signProfile_l1_le_half_activation security))
open _root_.P2M9e1cfc64 renaming h84 → _p2mH84
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h85 (security : ℕ) (profile : Palette security → ℝ) :
    (responseEquiv security).symm profile = profile -
      ((activation security + signFunctional (anchorSign security) (signProfile security))⁻¹ *
        signFunctional (anchorSign security) profile) • signProfile security :=
  _p2mH22 _ _ _ _ _ _
open _root_.P2M9e1cfc64 renaming h85 → _p2mH85
end
open _root_.P2M9e1cfc64 renaming h84 → _p2mH84
open _root_.P2M9e1cfc64 renaming h85 → _p2mH85
end CurrentAFT.FirstResponse
open _root_.P2M9e1cfc64 renaming h84 → _p2mH84
open _root_.P2M9e1cfc64 renaming h85 → _p2mH85
end
open _root_.P2M9e1cfc64 renaming h84 → _p2mH84
open _root_.P2M9e1cfc64 renaming h85 → _p2mH85
section
namespace CurrentAFT.ProposalSymmetry
open AFT DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.sourceCutoff Parameters.safeMargin DiffuseProfiles.activation
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h143 (modulus : ℕ) [NeZero modulus] (shift : ℤ) :
    shiftColor modulus (-shift) = -shiftColor modulus shift := by
  simp only [shiftColor, Int.cast_neg, map_neg]
open _root_.P2M9e1cfc64 renaming h143 → _p2mH143
set_option maxRecDepth 8192
private theorem _root_.P2M9e1cfc64.h555 (modulus : ℕ) [NeZero modulus] (shift : ℤ) (color : Fin modulus) :
    ((ZMod.finEquiv modulus).toEquiv.trans
      ((Equiv.addRight (shift : ZMod modulus)).trans (ZMod.finEquiv modulus).toEquiv.symm)) color =
        color + shiftColor modulus shift := by
  apply (ZMod.finEquiv modulus).injective
  change (ZMod.finEquiv modulus)
      ((ZMod.finEquiv modulus).symm ((ZMod.finEquiv modulus) color + (shift : ZMod modulus))) = _
  simp only [RingEquiv.apply_symm_apply, map_add, shiftColor]
open _root_.P2M9e1cfc64 renaming h555 → _p2mH555
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h144 (security : ℕ) (shift : ℤ) (color : Fin (Parameters.modulus security)) :
    shiftEquiv security shift color = color + shiftColor (Parameters.modulus security) shift :=
  _p2mH555 _ _ _
open _root_.P2M9e1cfc64 renaming h144 → _p2mH144
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h145 (security : ℕ) (shift : ℤ) (color : Fin (Parameters.modulus security)) :
    (shiftEquiv security shift).symm color = shiftEquiv security (-shift) color := by
  apply (shiftEquiv security shift).injective
  rw [Equiv.apply_symm_apply]
  simp only [_p2mH144, _p2mH143]
  abel
open _root_.P2M9e1cfc64 renaming h145 → _p2mH145
end
open _root_.P2M9e1cfc64 renaming h143 → _p2mH143
open _root_.P2M9e1cfc64 renaming h144 → _p2mH144
open _root_.P2M9e1cfc64 renaming h145 → _p2mH145
open _root_.P2M9e1cfc64 renaming h555 → _p2mH555
end CurrentAFT.ProposalSymmetry
open _root_.P2M9e1cfc64 renaming h143 → _p2mH143
open _root_.P2M9e1cfc64 renaming h144 → _p2mH144
open _root_.P2M9e1cfc64 renaming h145 → _p2mH145
open _root_.P2M9e1cfc64 renaming h555 → _p2mH555
end
open _root_.P2M9e1cfc64 renaming h145 → _p2mH145
open _root_.P2M9e1cfc64 renaming h143 → _p2mH143
open _root_.P2M9e1cfc64 renaming h144 → _p2mH144
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
theorem _root_.P2M9e1cfc64.h52 (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s')
    (colors : Fin (r + r') → Primary) (centers : Fin (s + s') → Body) :
    (homogeneousProduct primary body first second).val colors centers =
      ((r + r').factorial : ℝ)⁻¹ * ((s + s').factorial : ℝ)⁻¹ *
        ∑ primaryOrder : Equiv.Perm (Fin (r + r')), ∑ bodyOrder : Equiv.Perm (Fin (s + s')),
          finDisjointTensor first.val second.val (colors ∘ primaryOrder) (centers ∘ bodyOrder) := by
  exact (symmetrize_apply (finDisjointTensor first.val second.val) colors centers).trans (by
    simp only [Fintype.card_perm, Fintype.card_fin])
open _root_.P2M9e1cfc64 renaming h52 → _p2mH52
end
open _root_.P2M9e1cfc64 renaming h52 → _p2mH52
end CurrentAFT.ControlProduct
open _root_.P2M9e1cfc64 renaming h52 → _p2mH52
end
open _root_.P2M9e1cfc64 renaming h52 → _p2mH52
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
private theorem _root_.P2M9e1cfc64.h553 {Color : Type*} [Fintype Color] (law : FiniteDist Color)
    (hpositive : ∀ color, 0 < law.weight color) (source output : Color) :
    law.weight source * Hoeffding.centeredAtom law source output =
      (if output = source then 1 else 0) - law.weight source := by
  by_cases hequal : source = output
  · subst output
    simp only [Hoeffding.centeredAtom, if_true, mul_sub, mul_one,
      mul_inv_cancel₀ (hpositive source).ne']
  · simp only [Hoeffding.centeredAtom, hequal, Ne.symm hequal, if_false, zero_sub, mul_neg, mul_one]
open _root_.P2M9e1cfc64 renaming h553 → _p2mH553
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h51 {Color : Type*} [Fintype Color] (law : FiniteDist Color)
    (hpositive : ∀ color, 0 < law.weight color) {Index : Type*} [Fintype Index] [DecidableEq Index]
    (source output : Index → Color) :
    (∏ index, law.weight (source index)) *
        (∏ index, Hoeffding.centeredAtom law (source index) (output index)) =
      MixedKernel.canonicalPointBasis (fun _ : Index => law) source output := by
  rw [← Finset.prod_mul_distrib]
  simp only [_p2mH553 law hpositive, MixedKernel.canonicalPointBasis]
open _root_.P2M9e1cfc64 renaming h51 → _p2mH51
end
open _root_.P2M9e1cfc64 renaming h51 → _p2mH51
open _root_.P2M9e1cfc64 renaming h553 → _p2mH553
end CurrentAFT.CanonicalReconstruction
open _root_.P2M9e1cfc64 renaming h51 → _p2mH51
open _root_.P2M9e1cfc64 renaming h553 → _p2mH553
end
open _root_.P2M9e1cfc64 renaming h51 → _p2mH51
section
namespace CurrentAFT.BodyChannelEvaluation
open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundEvaluation BackgroundFirstEvaluation
  MarkedPairLeading LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference MarkedPairLeading.bodyConvolution
attribute [local instance] _root_.CurrentAFT.BodyChannelEvaluation.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h45 {State : Type*} [Fintype State] (law : FiniteDist State) (safe : State → Prop)
    (hzero : ∀ state, ¬safe state → law.weight state = 0) (density : State → ℝ) :
    weightedEmbedding (supportedLaw law safe hzero) Subtype.val (fun point => density point.val) =
      fun state => law.weight state * density state := by
  funext output
  calc
    _ = (supportedLaw law safe hzero).expectation (fun point => density point.val * (Pi.single point.val (1 : ℝ) : State → ℝ) output) := by
      unfold weightedEmbedding FiniteDist.expectation
      apply Finset.sum_congr rfl
      intro point _
      ring
    _ = law.expectation (fun point => density point * (Pi.single point (1 : ℝ) : State → ℝ) output) := supportedLaw_expectation law safe hzero
      (fun point : State => density point * (Pi.single point (1 : ℝ) : State → ℝ) output)
    _ = _ := by simp [FiniteDist.expectation, Pi.single_apply]
open _root_.P2M9e1cfc64 renaming h45 → _p2mH45
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h44 (security : ℕ) (density : ActualControls.Palette security → ℝ) :
    safeMass security (fun point => density point.val) = fun color => (centerLaw security).weight color * density color := by
  unfold safeMass bodyReference
  exact _p2mH45 _ _ _ density
open _root_.P2M9e1cfc64 renaming h44 → _p2mH44
end
open _root_.P2M9e1cfc64 renaming h44 → _p2mH44
open _root_.P2M9e1cfc64 renaming h45 → _p2mH45
end CurrentAFT.BodyChannelEvaluation
open _root_.P2M9e1cfc64 renaming h44 → _p2mH44
open _root_.P2M9e1cfc64 renaming h45 → _p2mH45
end
open _root_.P2M9e1cfc64 renaming h44 → _p2mH44
open _root_.P2M9e1cfc64 renaming h45 → _p2mH45
section
namespace CurrentAFT.BodyRootAverages
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram
  UniformBodyProfiles BackgroundCertificates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ProposalPrimary.safeLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h47 (security : ℕ) (law : FiniteDist (LocalReferenceEnergy.Palette security)) :
    rootAverage security law = (actualSeedLaw security).mix
      (fun seed => law.map (shiftEquiv security (actualBlur security seed))) := by
  ext output
  simp only [rootAverage, publicBlurLaw, actualSeedLaw, FiniteDist.mix_weight,
    Fintype.sum_prod_type, FiniteDist.prod_weight, FiniteDist.map_equiv_weight,
    actualBlur]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  ring
open _root_.P2M9e1cfc64 renaming h47 → _p2mH47
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h46 (security : ℕ) :
    rootAverage security (centerLaw security) = convolvedCenterLaw security :=
  _p2mH47 security (centerLaw security)
open _root_.P2M9e1cfc64 renaming h46 → _p2mH46
end
open _root_.P2M9e1cfc64 renaming h46 → _p2mH46
open _root_.P2M9e1cfc64 renaming h47 → _p2mH47
end CurrentAFT.BodyRootAverages
open _root_.P2M9e1cfc64 renaming h46 → _p2mH46
open _root_.P2M9e1cfc64 renaming h47 → _p2mH47
end
open _root_.P2M9e1cfc64 renaming h46 → _p2mH46
open _root_.P2M9e1cfc64 renaming h47 → _p2mH47
section
namespace CurrentAFT.ProtectedCycle
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h148 {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar]
    (reference : Index → FiniteDist Scalar) (first second : Index) (hdistinct : second ≠ first) :
    (FiniteDist.independent reference).map (fun latent => (latent first, latent second)) =
      (reference first).prod (reference second) := by
  ext values
  have htest := independent_pair_expectation reference first second hdistinct
    (fun firstValue secondValue => if (firstValue, secondValue) = values then 1 else 0)
  have hleft : (FiniteDist.independent reference).expectation
      (fun latent => if (latent first, latent second) = values then 1 else 0) =
      ((FiniteDist.independent reference).map
        (fun latent => (latent first, latent second))).weight values := by
    simp only [FiniteDist.expectation, FiniteDist.map_weight, mul_ite, mul_one, mul_zero]
    apply Finset.sum_congr rfl
    intro latent _
    by_cases hequal : (latent first, latent second) = values <;> simp [hequal]
  rw [hleft] at htest
  rw [htest]
  rcases values with ⟨firstValue, secondValue⟩
  simp [mul_ite, FiniteDist.prod_weight, ite_and]
open _root_.P2M9e1cfc64 renaming h148 → _p2mH148
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h146 {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (vertex : Fin body)
    (hdistinct : (finRotate body).symm vertex ≠ vertex) :
    (cycleLaw body modulus edgeLaw value).map (fun root => root vertex) =
      differenceLaw edgeLaw value := by
  unfold cycleLaw differenceLaw
  rw [FiniteDist.map_map]
  have hpair := _p2mH148 (fun _ : Fin body => edgeLaw) vertex
    ((finRotate body).symm vertex) hdistinct
  rw [← hpair, FiniteDist.map_map]
  rfl
open _root_.P2M9e1cfc64 renaming h146 → _p2mH146
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h147 {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (hbody : 2 ≤ body) (vertex : Fin body) :
    (cycleLaw body modulus edgeLaw value).map (fun root => root vertex) =
      differenceLaw edgeLaw value :=
  _p2mH146 body modulus edgeLaw value vertex (cycle_predecessor_ne body hbody vertex)
open _root_.P2M9e1cfc64 renaming h147 → _p2mH147
end
open _root_.P2M9e1cfc64 renaming h146 → _p2mH146
open _root_.P2M9e1cfc64 renaming h147 → _p2mH147
open _root_.P2M9e1cfc64 renaming h148 → _p2mH148
end CurrentAFT.ProtectedCycle
open _root_.P2M9e1cfc64 renaming h146 → _p2mH146
open _root_.P2M9e1cfc64 renaming h147 → _p2mH147
open _root_.P2M9e1cfc64 renaming h148 → _p2mH148
end
open _root_.P2M9e1cfc64 renaming h148 → _p2mH148
open _root_.P2M9e1cfc64 renaming h147 → _p2mH147
open _root_.P2M9e1cfc64 renaming h146 → _p2mH146
section
namespace CurrentAFT.CycleSelections
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h80 {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : Selection body order) (slot : Fin order) :
    (selectedLaw body order modulus source value sites).map (fun root => root slot) =
      ProtectedCycle.differenceLaw source value := by
  rw [selectedLaw, FiniteDist.map_map]
  exact _p2mH147 body modulus source value hbody (sites slot)
open _root_.P2M9e1cfc64 renaming h80 → _p2mH80
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h79 {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (horder : order ≤ body) (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus) (slot : Fin order) :
    (averagedSelectedLaw body order modulus horder source value).map (fun root => root slot) =
      ProtectedCycle.differenceLaw source value := by
  rw [averagedSelectedLaw, FiniteDist.map_mix]
  simp_rw [_p2mH80 body order modulus hbody source value]
  exact FiniteDist.mix_const _ _
open _root_.P2M9e1cfc64 renaming h79 → _p2mH79
end
open _root_.P2M9e1cfc64 renaming h79 → _p2mH79
open _root_.P2M9e1cfc64 renaming h80 → _p2mH80
end CurrentAFT.CycleSelections
open _root_.P2M9e1cfc64 renaming h79 → _p2mH79
open _root_.P2M9e1cfc64 renaming h80 → _p2mH80
end
open _root_.P2M9e1cfc64 renaming h80 → _p2mH80
open _root_.P2M9e1cfc64 renaming h79 → _p2mH79
section
namespace CurrentAFT.CycleRootExpansion
open AFT CycleSelections
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Index Color Value : Type*} [Fintype Index] [DecidableEq Index] [Fintype Color]
  [AddCommGroup Value] [Module ℝ Value]
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h77 (joint : FiniteDist (Index → Color))
    (reference : Index → FiniteDist Color)
    (hmarginal : ∀ index, joint.map (fun word => word index) = reference index)
    (word : Index → Color) (hword : joint.weight word ≠ 0) (index : Index) :
    0 < (reference index).weight (word index) := by
  have hpositive : 0 < joint.weight word := lt_of_le_of_ne (joint.nonneg word) (Ne.symm hword)
  rw [← hmarginal index, FiniteDist.map_weight]
  apply hpositive.trans_le
  apply (Finset.single_le_sum (s := Finset.univ)
    (f := fun input => if input index = word index then joint.weight input else 0)
    (fun input _ => by split_ifs; exact joint.nonneg input; exact le_rfl)
    (Finset.mem_univ word)).trans'
  simp only [if_true, le_refl]
open _root_.P2M9e1cfc64 renaming h77 → _p2mH77
section Actual
attribute [local instance] _root_.CurrentAFT.CycleRootExpansion.currentModulusNeZero
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h76 (security : ℕ) : 2 ≤ Parameters.bodySize security := by
  have hbase := Parameters.base_ge_two security
  have hmod := (Parameters.modulus_spec security).2.two_le
  have hpower : 1 ≤ Parameters.base security ^ 96 := one_le_pow₀ (by omega)
  rw [Parameters.bodySize_eq]
  exact hmod.trans (by simpa using Nat.mul_le_mul_left (Parameters.modulus security) hpower)
open _root_.P2M9e1cfc64 renaming h76 → _p2mH76
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h78 (security : ℕ) (index : Vertex security) :
    (rootLaw security).map (fun roots => roots index) = rootReference security := by
  let labels : Selection (Parameters.bodySize security) 1 :=
    ⟨fun _ => index, fun first second _ => Subsingleton.elim first second⟩
  have h := congrArg (fun law : FiniteDist (Fin 1 → Root security) =>
    law.map (fun roots => roots 0))
    (rootLaw_selected security 1 (by have := _p2mH76 security; omega) labels)
  rw [FiniteDist.map_map] at h
  exact h.trans (_p2mH79 _ _ _ _
    (_p2mH76 security) _ _ 0)
open _root_.P2M9e1cfc64 renaming h78 → _p2mH78
variable {Control : Type*} [Fintype Control]
end Actual
open _root_.P2M9e1cfc64 renaming h76 → _p2mH76
open _root_.P2M9e1cfc64 renaming h78 → _p2mH78
end
open _root_.P2M9e1cfc64 renaming h76 → _p2mH76
open _root_.P2M9e1cfc64 renaming h77 → _p2mH77
open _root_.P2M9e1cfc64 renaming h78 → _p2mH78
end CurrentAFT.CycleRootExpansion
open _root_.P2M9e1cfc64 renaming h76 → _p2mH76
open _root_.P2M9e1cfc64 renaming h77 → _p2mH77
open _root_.P2M9e1cfc64 renaming h78 → _p2mH78
end
open _root_.P2M9e1cfc64 renaming h76 → _p2mH76
open _root_.P2M9e1cfc64 renaming h77 → _p2mH77
open _root_.P2M9e1cfc64 renaming h78 → _p2mH78
section
namespace CurrentAFT.RootIndependentBackground
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  LocalReferenceEnergy ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  BackgroundPolynomialEvaluation BackgroundEndpointLaw RootBackgroundPolynomial
  CycleRootExpansion CycleRootPolynomial BodyRootAverages PairQuadraticEvaluation
  PositiveFirstCoefficient LegPolynomialEvaluation BackgroundTranslations
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
  CycleRootExpansion.rootLaw CycleRootExpansion.rootReference
attribute [local instance] _root_.CurrentAFT.RootIndependentBackground.finOneDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentBackground.finThreeDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentBackground.blockIndexDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h483 {Input Output State : Type*} [Fintype Input] [Fintype Output] [Fintype State]
    (law : FiniteDist Input) (map : Input → Output) (kernel : Output → FiniteDist State) :
    (law.map map).mix kernel = law.mix (kernel ∘ map) := by
  ext state
  change (law.map map).expectation (fun output => (kernel output).weight state) =
    law.expectation (fun input => (kernel (map input)).weight state)
  rw [FiniteDist.expectation_map]
  rfl
open _root_.P2M9e1cfc64 renaming h483 → _p2mH483
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h484 (security : ℕ) (law : FiniteDist (ActualControls.Palette security)) :
    (rootReference security).mix (fun root => law.map (shiftEquiv security (root.val : ℤ))) =
      rootAverage security law := by
  unfold rootReference ProtectedCycle.differenceLaw
  rw [_p2mH483]
  have hshift (edge : BlurSeed security) :
      shiftEquiv security
        (((((edge.1 : ℤ) : Root security) - ((edge.2 : ℤ) : Root security)).val : ℕ) : ℤ) =
        shiftEquiv security (edge.1.val - edge.2.val) := by
    apply shiftEquiv_eq_of_cast
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_sub]
  ext output
  simp only [FiniteDist.mix_weight, Function.comp_apply, hshift,
    rootAverage, publicBlurLaw, Fintype.sum_prod_type, FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring
open _root_.P2M9e1cfc64 renaming h484 → _p2mH484
end
open _root_.P2M9e1cfc64 renaming h483 → _p2mH483
open _root_.P2M9e1cfc64 renaming h484 → _p2mH484
end CurrentAFT.RootIndependentBackground
open _root_.P2M9e1cfc64 renaming h483 → _p2mH483
open _root_.P2M9e1cfc64 renaming h484 → _p2mH484
end
open _root_.P2M9e1cfc64 renaming h483 → _p2mH483
open _root_.P2M9e1cfc64 renaming h484 → _p2mH484
section
namespace CurrentAFT.RootCoordinateProjection
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {Index Root Control : Type*} [Fintype Index] [DecidableEq Index]
  [Fintype Root] [Fintype Control]
set_option maxRecDepth 8192
omit [Fintype Index] [Fintype Control] in
theorem _root_.P2M9e1cfc64.h480 (root : FiniteDist Root) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ)
    (hinvariant : ∀ sample value, score (Function.update sample.1 index value, sample.2) = score sample) :
    average root index score = score := by
  funext sample
  simp only [average_apply, hinvariant, FiniteDist.expectation_const]
open _root_.P2M9e1cfc64 renaming h480 → _p2mH480
set_option maxRecDepth 8192
omit [Fintype Index] [Fintype Control] in
theorem _root_.P2M9e1cfc64.h481 (root : FiniteDist Root) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ)
    (hcentered : ∀ sample : Input (Index := Index) (Root := Root) (Control := Control), root.expectation (fun value => score (Function.update sample.1 index value, sample.2)) = 0) :
    center root index score = score := by
  funext sample
  simp only [center_apply, average_apply, hcentered, sub_zero]
open _root_.P2M9e1cfc64 renaming h481 → _p2mH481
set_option maxRecDepth 8192
omit [Fintype Index] [Fintype Control] in
theorem _root_.P2M9e1cfc64.h482 (root : FiniteDist Root) (coordinates : List (Index × Bool))
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ)
    (hfixed : ∀ item ∈ coordinates, coordinate root item.1 item.2 score = score) :
    sequence root coordinates score = score := by
  induction coordinates with
  | nil => rfl
  | cons item rest ih =>
    change coordinate root item.1 item.2 (sequence root rest score) = score
    rw [ih (fun other hother => hfixed other (List.mem_cons_of_mem item hother))]
    exact hfixed item List.mem_cons_self
open _root_.P2M9e1cfc64 renaming h482 → _p2mH482
end
open _root_.P2M9e1cfc64 renaming h480 → _p2mH480
open _root_.P2M9e1cfc64 renaming h481 → _p2mH481
open _root_.P2M9e1cfc64 renaming h482 → _p2mH482
end CurrentAFT.RootCoordinateProjection
open _root_.P2M9e1cfc64 renaming h480 → _p2mH480
open _root_.P2M9e1cfc64 renaming h481 → _p2mH481
open _root_.P2M9e1cfc64 renaming h482 → _p2mH482
end
open _root_.P2M9e1cfc64 renaming h480 → _p2mH480
open _root_.P2M9e1cfc64 renaming h482 → _p2mH482
open _root_.P2M9e1cfc64 renaming h481 → _p2mH481
section
namespace CurrentAFT.SelectedOrdinaryMean
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm GradedControlStability
  LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds CoefficientHilbert SelectedOrdinaryRoot
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.SelectedOrdinaryMean.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.SelectedOrdinaryMean.safeDecidableEq
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h539 (security : ℕ) (root : Root security) (score : SafePalette security → ℝ)
    (output : Palette security) :
    pushLinear (bodyReference security) (rootEmbedding security root) score output =
      BodyChannelEvaluation.safeMass security score ((shiftEquiv security (root.val : ℤ)).symm output) := by
  unfold pushLinear rootEmbedding BodyChannelEvaluation.safeMass BodyChannelEvaluation.weightedEmbedding
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro center _
  have hequal : shiftEquiv security (root.val : ℤ) center.val = output ↔
      (shiftEquiv security (root.val : ℤ)).symm output = center.val := by
    constructor
    · intro h; exact ((shiftEquiv security (root.val : ℤ)).symm_apply_eq.mpr h.symm)
    · intro h; exact (Equiv.apply_eq_iff_eq_symm_apply (shiftEquiv security (root.val : ℤ))).mpr h.symm
  by_cases h : shiftEquiv security (root.val : ℤ) center.val = output
  · rw [if_pos h, if_pos (hequal.mp h), mul_one]
  · rw [if_neg h, if_neg (fun h' => h (hequal.mpr h')), mul_zero]
open _root_.P2M9e1cfc64 renaming h539 → _p2mH539
end
open _root_.P2M9e1cfc64 renaming h539 → _p2mH539
end CurrentAFT.SelectedOrdinaryMean
open _root_.P2M9e1cfc64 renaming h539 → _p2mH539
end
open _root_.P2M9e1cfc64 renaming h539 → _p2mH539
section
namespace CurrentAFT.RootTaggedLocal
open AFT DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  UniformBodyProfiles CycleRootExpansion RootBackgroundPolynomial PrimaryTensorInverse
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  CycleRootExpansion.rootReference
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h533 (security : ℕ) (role : BodyRole) (queue : ℤ) (color : ActualControls.Palette security) :
    (rootReference security).expectation (fun root => deviationProfile security role queue root color) = 0 := by
  simp only [FiniteDist.expectation, deviationProfile, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, FiniteDist.sum_one, one_mul, meanLaw, FiniteDist.mix_weight, sub_self]
open _root_.P2M9e1cfc64 renaming h533 → _p2mH533
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h535 (security : ℕ) (role : BodyRole) (queue : ℤ) :
    rootMass security role queue (fun _ => 1) = 0 := by
  funext color
  simpa only [rootMass, LinearMap.coe_mk, AddHom.coe_mk, mul_one, FiniteDist.expectation, Pi.zero_apply] using
    _p2mH533 security role queue color
open _root_.P2M9e1cfc64 renaming h535 → _p2mH535
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h534 (security : ℕ) (role : BodyRole) (queue : ℤ) :
    rootLift security role queue (fun _ => 1) = 0 := by
  rw [rootLift_apply, _p2mH535, map_zero, map_zero]
open _root_.P2M9e1cfc64 renaming h534 → _p2mH534
end
open _root_.P2M9e1cfc64 renaming h533 → _p2mH533
open _root_.P2M9e1cfc64 renaming h534 → _p2mH534
open _root_.P2M9e1cfc64 renaming h535 → _p2mH535
end CurrentAFT.RootTaggedLocal
open _root_.P2M9e1cfc64 renaming h533 → _p2mH533
open _root_.P2M9e1cfc64 renaming h534 → _p2mH534
open _root_.P2M9e1cfc64 renaming h535 → _p2mH535
end
open _root_.P2M9e1cfc64 renaming h535 → _p2mH535
open _root_.P2M9e1cfc64 renaming h534 → _p2mH534
open _root_.P2M9e1cfc64 renaming h533 → _p2mH533
section
namespace CurrentAFT.RootTaggedFamilies
open AFT ControlCoordinates GradedControlAlgebra GradedControlNorm DiffuseProfiles
  ProposalPrimary ActualControls UniformBodyProfiles CycleRootExpansion RootTaggedLocal
  BackgroundFamilies BackgroundRates BackgroundEvaluation BackgroundFirstEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  ActualControls.bodyReference CycleRootExpansion.rootReference
attribute [local instance] _root_.CurrentAFT.RootTaggedFamilies.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h531 (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    rootFamilyLinear security order horder role queue (fun _ => 1) = 0 := by
  funext arity
  by_cases hequal : arity = BackgroundFamilies.primaryArity order horder
  · subst arity
    simp only [rootFamilyLinear, LinearMap.comp_apply, LinearMap.single_apply, Pi.single_eq_same, Pi.zero_apply]
    change rootKernelLinear security role queue (fun _ => 1) = 0
    apply Subtype.ext
    funext colors centers
    exact congrFun (_p2mH534 security role queue) (colors 0)
  · simp only [rootFamilyLinear, LinearMap.comp_apply, LinearMap.single_apply, Pi.zero_apply]
    exact Pi.single_eq_of_ne (M := fun arity : TruncatedArity order =>
      canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val) hequal _
open _root_.P2M9e1cfc64 renaming h531 → _p2mH531
end
open _root_.P2M9e1cfc64 renaming h531 → _p2mH531
end CurrentAFT.RootTaggedFamilies
open _root_.P2M9e1cfc64 renaming h531 → _p2mH531
end
open _root_.P2M9e1cfc64 renaming h531 → _p2mH531
section
namespace CurrentAFT.RootTaggedLegHigher
open AFT DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  ActualBlockFock PositiveFirstCoefficient CycleRootExpansion RootTaggedLocal
  PrimaryTensorInverse PhysicalBlockTensors BlockFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  CycleRootExpansion.rootReference
attribute [local instance] _root_.CurrentAFT.RootTaggedLegHigher.finThreeDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h532 (security : ℕ) : massLinear security (fun _ => 1) = 0 := by
  have hcenter : TensorChannel.center (rootReference security) (fun _ => 1) = 0 := by
    funext root
    simp only [TensorChannel.center_apply, FiniteDist.expectation_const, sub_self, Pi.zero_apply]
  rw [massLinear, LinearMap.comp_apply, hcenter, map_zero]
open _root_.P2M9e1cfc64 renaming h532 → _p2mH532
end
open _root_.P2M9e1cfc64 renaming h532 → _p2mH532
end CurrentAFT.RootTaggedLegHigher
open _root_.P2M9e1cfc64 renaming h532 → _p2mH532
end
open _root_.P2M9e1cfc64 renaming h532 → _p2mH532
section
namespace CurrentAFT.SelectedRootComponent
open AFT CycleSelections CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize
attribute [local instance] _root_.CurrentAFT.SelectedRootComponent.currentModulusNeZero
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h540 (security count : ℕ)
    (labels : CycleSelections.Selection (Parameters.bodySize security) count) (index : Fin count) :
    Hoeffding.CenteredAt (fun _ => rootReference security) index
      (selectedCoefficient security count labels) := by
  let joint := (rootLaw security).map (fun roots slot => roots (labels slot))
  have hmarginal (slot : Fin count) :
      joint.map (fun roots => roots slot) = rootReference security := by
    dsimp only [joint]
    rw [FiniteDist.map_map]
    exact _p2mH78 security (labels slot)
  have hcanonical := SupportedHoeffding.densityComponent_canonical_of_support
    (fun _ : Fin count => rootReference security) joint.weight
    (_p2mH77 joint (fun _ => rootReference security) hmarginal) Finset.univ
  have hequal : selectedCoefficient security count labels =
      Hoeffding.densityComponent (fun _ : Fin count => rootReference security) joint.weight Finset.univ := by
    funext word
    simp only [selectedCoefficient, centeredRootDensity, FiniteDist.expectation,
      Hoeffding.densityComponent, SupportedHoeffding.centeredRootAtom_eq, joint]
    congr 3
    exact Subsingleton.elim _ _
  rw [hequal]
  exact hcanonical.2 index (Finset.mem_univ index)
open _root_.P2M9e1cfc64 renaming h540 → _p2mH540
end
open _root_.P2M9e1cfc64 renaming h540 → _p2mH540
end CurrentAFT.SelectedRootComponent
open _root_.P2M9e1cfc64 renaming h540 → _p2mH540
end
open _root_.P2M9e1cfc64 renaming h540 → _p2mH540
section
namespace CurrentAFT.PairedRootCentering
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  ControlCoordinates RaisingPatternBudget
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.PairedRootCentering.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootCentering.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootCentering.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h132 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (index : Fin tagged.card) :
    Hoeffding.CenteredAt (fun _ => CycleRootExpansion.rootReference security)
      (sourceEmbedding selection tagged index) (rootDensity selection tagged layout) := by
  intro roots
  change (∑ root, (CycleRootExpansion.rootReference security).weight root *
    CycleRootExpansion.selectedCoefficient security tagged.card (labels tagged layout)
      (Function.update roots (sourceEmbedding selection tagged index) root ∘ sourceEmbedding selection tagged)) = 0
  simp_rw [Function.update_comp_eq_of_injective roots (sourceEmbedding selection tagged).injective]
  have h := _p2mH540 security tagged.card (labels tagged layout) index
  convert h (roots ∘ sourceEmbedding selection tagged) using 1
open _root_.P2M9e1cfc64 renaming h132 → _p2mH132
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h133 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (slot : Sigma (groupRootSlots selection tagged)) (hslot : slot ∉ Set.range (sourceEmbedding selection tagged))
    (roots : Sigma (groupRootSlots selection tagged) → CycleRootExpansion.Root security)
    (root : CycleRootExpansion.Root security) :
    rootDensity selection tagged layout (Function.update roots slot root) = rootDensity selection tagged layout roots := by
  unfold rootDensity
  rw [Function.update_comp_eq_of_forall_ne roots root]
  intro index hequal
  exact hslot ⟨index, hequal⟩
open _root_.P2M9e1cfc64 renaming h133 → _p2mH133
end
open _root_.P2M9e1cfc64 renaming h132 → _p2mH132
open _root_.P2M9e1cfc64 renaming h133 → _p2mH133
end CurrentAFT.PairedRootCentering
open _root_.P2M9e1cfc64 renaming h132 → _p2mH132
open _root_.P2M9e1cfc64 renaming h133 → _p2mH133
end
open _root_.P2M9e1cfc64 renaming h132 → _p2mH132
open _root_.P2M9e1cfc64 renaming h133 → _p2mH133
section
namespace CurrentAFT.GroupedRootUpdates
open AFT GroupedSourceNorm
open scoped Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.GroupedRootUpdates.classicalSigmaDecidableEq
variable {Group Root : Type*} [DecidableEq Group] (Slots Control : Group → Type*)
  [∀ group, DecidableEq (Slots group)]
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h95 (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (slot : Slots group) (value : Root) :
    roots Slots Control (updateRoot Slots Control word group slot value) =
      Function.update (roots Slots Control word) ⟨group, slot⟩ value := by
  funext point
  rcases point with ⟨other, point⟩
  by_cases hequal : other = group
  · subst other
    by_cases hslot : point = slot
    · subst point
      simp [roots, updateRoot]
    · simp [roots, updateRoot, hslot]
  · simp [roots, updateRoot, hequal]
open _root_.P2M9e1cfc64 renaming h95 → _p2mH95
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h94 (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (slot : Slots group) (value : Root) :
    controls Slots Control (updateRoot Slots Control word group slot value) = controls Slots Control word := by
  funext other
  by_cases hequal : other = group
  · subst other
    simp [controls, updateRoot]
  · simp [controls, updateRoot, hequal]
open _root_.P2M9e1cfc64 renaming h94 → _p2mH94
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h96 (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (sample : (Slots group → Root) × Control group) (slot : Slots group) (value : Root) :
    updateRoot Slots Control (Function.update word group sample) group slot value =
      Function.update word group (Function.update sample.1 slot value, sample.2) := by
  simp only [updateRoot, Function.update_self, Function.update_idem]
open _root_.P2M9e1cfc64 renaming h96 → _p2mH96
end
open _root_.P2M9e1cfc64 renaming h94 → _p2mH94
open _root_.P2M9e1cfc64 renaming h95 → _p2mH95
open _root_.P2M9e1cfc64 renaming h96 → _p2mH96
end CurrentAFT.GroupedRootUpdates
open _root_.P2M9e1cfc64 renaming h94 → _p2mH94
open _root_.P2M9e1cfc64 renaming h95 → _p2mH95
open _root_.P2M9e1cfc64 renaming h96 → _p2mH96
end
open _root_.P2M9e1cfc64 renaming h95 → _p2mH95
open _root_.P2M9e1cfc64 renaming h96 → _p2mH96
open _root_.P2M9e1cfc64 renaming h94 → _p2mH94
section
namespace CurrentAFT.DependentTensorComposition
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input Middle Output : Index → Type*}
  [∀ index, Fintype (Input index)] [∀ index, Fintype (Middle index)] [∀ index, Fintype (Output index)]
set_option maxRecDepth 8192
omit [∀ index, Fintype (Output index)] in
theorem _root_.P2M9e1cfc64.h81
    (first : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Middle index → ℝ))
    (second : ∀ index, (Middle index → ℝ) →ₗ[ℝ] (Output index → ℝ))
    (input : ((index : Index) → Input index) → ℝ) :
    DependentTensorChannel.apply (fun index => (second index).comp (first index)) input =
      DependentTensorChannel.apply second (DependentTensorChannel.apply first input) := by
  funext output
  unfold DependentTensorChannel.apply
  simp only [LinearMap.comp_apply]
  have hcolumn (index : Index) (source : Input index) :
      second index (first index (Pi.single source 1)) (output index) =
        ∑ middle, first index (Pi.single source 1) middle *
          second index (Pi.single middle 1) (output index) :=
    TensorChannel.channel_sum_single (second index) _ _
  simp_rw [hcolumn]
  simp_rw [Fintype.prod_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro middle _
  apply Finset.sum_congr rfl
  intro source _
  rw [Finset.prod_mul_distrib]
  ring
open _root_.P2M9e1cfc64 renaming h81 → _p2mH81
end
open _root_.P2M9e1cfc64 renaming h81 → _p2mH81
end CurrentAFT.DependentTensorComposition
open _root_.P2M9e1cfc64 renaming h81 → _p2mH81
end
open _root_.P2M9e1cfc64 renaming h81 → _p2mH81
namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.DependentTensorComposition
end CurrentAFT.DependentTensorComposition
section
namespace CurrentAFT.DependentTensorFixedInput
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h82 (count : ℕ) {Input : Fin count → Type*}
    (projector : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Input index → ℝ))
    (kernel : ((index : Fin count) → Input index) → ℝ)
    (hfixed : ∀ index word, projector index
      (fun value => kernel (Function.update word index value)) =
        fun value => kernel (Function.update word index value)) :
    DependentTensorChannel.applyFin count projector kernel = kernel := by
  induction count with
  | zero =>
      funext word
      change kernel (fun index => Fin.elim0 index) = kernel word
      congr 1
      funext index
      exact Fin.elim0 index
  | succ count ih =>
      have htail (first : Input 0) :
          ∀ index word, projector index.succ
            (fun value => kernel (Fin.cons first (Function.update word index value))) =
              fun value => kernel (Fin.cons first (Function.update word index value)) := by
        intro index word
        simpa only [Fin.cons_update] using hfixed index.succ (Fin.cons first word)
      have ht (first : Input 0) :
          DependentTensorChannel.applyFin count (fun index => projector index.succ)
            (fun rest => kernel (Fin.cons first rest)) =
              fun rest => kernel (Fin.cons first rest) :=
        ih (fun index => projector index.succ) (fun rest => kernel (Fin.cons first rest))
          (htail first)
      funext output
      change projector 0 (fun first =>
        DependentTensorChannel.applyFin count (fun index => projector index.succ)
          (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ))
            (output 0) = kernel output
      simp_rw [ht]
      have hcons : Fin.cons (output 0) (fun index => output index.succ) = output := by
        funext index
        refine Fin.cases ?_ (fun index => ?_) index <;> rfl
      have hh := congrFun (hfixed 0
        (Fin.cons (output 0) (fun index => output index.succ))) (output 0)
      simp only [Fin.update_cons_zero] at hh
      rw [hcons] at hh
      exact hh
open _root_.P2M9e1cfc64 renaming h82 → _p2mH82
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input : Index → Type*} [∀ index, Fintype (Input index)]
set_option maxRecDepth 8192
omit [Fintype Index] [∀ index, Fintype (Input index)] in
private theorem _root_.P2M9e1cfc64.h554 {Index' : Type*} [DecidableEq Index']
    (equiv : Index' ≃ Index) (word : ∀ index, Input (equiv index))
    (index : Index') (value : Input (equiv index)) :
    Equiv.piCongrLeft Input equiv (Function.update word index value) =
      Function.update (Equiv.piCongrLeft Input equiv word) (equiv index) value := by
  simpa only [Equiv.piCongrLeft, Equiv.symm_symm] using
    Function.piCongrLeft'_symm_update Input equiv.symm word index value
open _root_.P2M9e1cfc64 renaming h554 → _p2mH554
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h83
    (projector : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Input index → ℝ))
    (kernel : ((index : Index) → Input index) → ℝ)
    (hfixed : ∀ index word, projector index
      (fun value => kernel (Function.update word index value)) =
        fun value => kernel (Function.update word index value)) :
    DependentTensorChannel.apply projector kernel = kernel := by
  let equiv : Fin (Fintype.card Index) ≃ Index := (Fintype.equivFin Index).symm
  have hfixed' (index : Fin (Fintype.card Index)) (word : ∀ index, Input (equiv index)) :
      projector (equiv index)
        (fun value => kernel (Equiv.piCongrLeft Input equiv (Function.update word index value))) =
          fun value => kernel (Equiv.piCongrLeft Input equiv (Function.update word index value)) := by
    simpa only [_p2mH554] using
      hfixed (equiv index) (Equiv.piCongrLeft Input equiv word)
  have hh := _p2mH82 (Fintype.card Index) (fun index => projector (equiv index))
    (fun word => kernel (Equiv.piCongrLeft Input equiv word)) hfixed'
  funext output
  have heq := congrFun hh ((Equiv.piCongrLeft Input equiv).symm output)
  rw [DependentTensorChannel.applyFin_formula] at heq
  have hreindex :
      (∑ point : (index : Fin (Fintype.card Index)) → Input (equiv index),
        kernel (Equiv.piCongrLeft Input equiv point) *
          ∏ index, projector (equiv index) (Pi.single (point index) 1)
            (((Equiv.piCongrLeft Input equiv).symm output) index)) =
        DependentTensorChannel.apply projector kernel output := by
    unfold DependentTensorChannel.apply
    rw [← (Equiv.piCongrLeft Input equiv).sum_comp]
    apply Finset.sum_congr rfl
    intro point _
    congr 1
    rw [← equiv.prod_comp]
    simp only [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_symm_apply]
  rw [hreindex] at heq
  simpa only [Equiv.apply_symm_apply] using heq
open _root_.P2M9e1cfc64 renaming h83 → _p2mH83
end
open _root_.P2M9e1cfc64 renaming h82 → _p2mH82
open _root_.P2M9e1cfc64 renaming h83 → _p2mH83
open _root_.P2M9e1cfc64 renaming h554 → _p2mH554
end CurrentAFT.DependentTensorFixedInput
open _root_.P2M9e1cfc64 renaming h82 → _p2mH82
open _root_.P2M9e1cfc64 renaming h83 → _p2mH83
open _root_.P2M9e1cfc64 renaming h554 → _p2mH554
end
open _root_.P2M9e1cfc64 renaming h83 → _p2mH83
open _root_.P2M9e1cfc64 renaming h82 → _p2mH82
namespace CurrentAFT.DependentTensorFixedInput
end CurrentAFT.DependentTensorFixedInput
section
namespace CurrentAFT.PairedRootProjection
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  PairedRootCentering ControlCoordinates GroupedRootUpdates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.PairedRootProjection.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootProjection.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootProjection.classicalSigmaDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootProjection.slotDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h137 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (slot : Sigma (groupRootSlots selection tagged)) :
    slot ∈ Set.range (sourceEmbedding selection tagged) ↔ rootEmbedding selection tagged slot ∈ tagged := by
  constructor
  · rintro ⟨index, rfl⟩
    change rootEmbedding selection tagged (tagEmbedding selection tagged (tagged.equivFin.symm index)) ∈ tagged
    rw [tag_image]
    exact (tagged.equivFin.symm index).property
  · intro hslot
    refine ⟨tagged.equivFin ⟨rootEmbedding selection tagged slot, hslot⟩, ?_⟩
    apply (rootEmbedding selection tagged).injective
    simp only [sourceEmbedding, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.symm_apply_apply, tag_image]
open _root_.P2M9e1cfc64 renaming h137 → _p2mH137
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h134 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (word : GroupInput selection tagged) :
    jointInput selection tagged layout kernel word =
      rootDensity selection tagged layout (roots (groupRootSlots selection tagged) (ControlInput selection tagged) word) *
        controlKernel selection tagged kernel (controls (groupRootSlots selection tagged) (ControlInput selection tagged) word) := rfl
open _root_.P2M9e1cfc64 renaming h134 → _p2mH134
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h138 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (word : GroupInput selection tagged) (group : ActiveGroup selection tagged)
    (slot : groupRootSlots selection tagged group)
    (htag : rootEmbedding selection tagged ⟨group, slot⟩ ∈ tagged) :
    (CycleRootExpansion.rootReference security).expectation (fun value =>
      jointInput selection tagged layout kernel
        (updateRoot (groupRootSlots selection tagged) (ControlInput selection tagged) word group slot value)) = 0 := by
  obtain ⟨index, hindex⟩ := (_p2mH137 selection tagged ⟨group, slot⟩).mpr htag
  simp_rw [_p2mH134, _p2mH95, _p2mH94]
  rw [← hindex]
  unfold FiniteDist.expectation
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, _p2mH132 selection tagged layout index, zero_mul]
open _root_.P2M9e1cfc64 renaming h138 → _p2mH138
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h139 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (word : GroupInput selection tagged) (group : ActiveGroup selection tagged)
    (slot : groupRootSlots selection tagged group)
    (htag : rootEmbedding selection tagged ⟨group, slot⟩ ∉ tagged) (value : CycleRootExpansion.Root security) :
    jointInput selection tagged layout kernel
      (updateRoot (groupRootSlots selection tagged) (ControlInput selection tagged) word group slot value) =
        jointInput selection tagged layout kernel word := by
  rw [_p2mH134, _p2mH95, _p2mH94, _p2mH134]
  rw [_p2mH133 selection tagged layout ⟨group, slot⟩
    (fun h => htag ((_p2mH137 selection tagged ⟨group, slot⟩).mp h))]
open _root_.P2M9e1cfc64 renaming h139 → _p2mH139
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h136 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (word : GroupInput selection tagged) (group : ActiveGroup selection tagged) :
    projector selection tagged group (fun sample => jointInput selection tagged layout kernel (Function.update word group sample)) =
      fun sample => jointInput selection tagged layout kernel (Function.update word group sample) := by
  apply _p2mH482
  intro item hitem
  obtain ⟨slot, _, rfl⟩ := List.mem_map.mp hitem
  by_cases htag : rootEmbedding selection tagged ⟨group, slot⟩ ∈ tagged
  · simp only [htag, decide_true, RootCoordinateProjection.coordinate, if_true]
    apply _p2mH481
    intro sample
    simp_rw [← _p2mH96]
    exact _p2mH138 selection tagged layout kernel (Function.update word group sample) group slot htag
  · simp only [htag, decide_false, RootCoordinateProjection.coordinate, Bool.false_eq_true, if_false]
    apply _p2mH480
    intro sample value
    rw [← _p2mH96]
    exact _p2mH139 selection tagged layout kernel (Function.update word group sample) group slot htag value
open _root_.P2M9e1cfc64 renaming h136 → _p2mH136
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h135 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    DependentTensorChannel.apply (projector selection tagged) (jointInput selection tagged layout kernel) =
      jointInput selection tagged layout kernel :=
  _p2mH83 _ _ (fun group word =>
    _p2mH136 selection tagged layout kernel word group)
open _root_.P2M9e1cfc64 renaming h135 → _p2mH135
end
open _root_.P2M9e1cfc64 renaming h134 → _p2mH134
open _root_.P2M9e1cfc64 renaming h135 → _p2mH135
open _root_.P2M9e1cfc64 renaming h136 → _p2mH136
open _root_.P2M9e1cfc64 renaming h137 → _p2mH137
open _root_.P2M9e1cfc64 renaming h138 → _p2mH138
open _root_.P2M9e1cfc64 renaming h139 → _p2mH139
end CurrentAFT.PairedRootProjection
open _root_.P2M9e1cfc64 renaming h134 → _p2mH134
open _root_.P2M9e1cfc64 renaming h135 → _p2mH135
open _root_.P2M9e1cfc64 renaming h136 → _p2mH136
open _root_.P2M9e1cfc64 renaming h137 → _p2mH137
open _root_.P2M9e1cfc64 renaming h138 → _p2mH138
open _root_.P2M9e1cfc64 renaming h139 → _p2mH139
end
open _root_.P2M9e1cfc64 renaming h138 → _p2mH138
open _root_.P2M9e1cfc64 renaming h134 → _p2mH134
open _root_.P2M9e1cfc64 renaming h139 → _p2mH139
open _root_.P2M9e1cfc64 renaming h136 → _p2mH136
open _root_.P2M9e1cfc64 renaming h135 → _p2mH135
open _root_.P2M9e1cfc64 renaming h137 → _p2mH137
section
namespace CurrentAFT.GroupedFamilyComposition
open AFT ControlCoordinates ControlProduct GradedControlAlgebra GroupedFamilyTensor
  GroupedKernelNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.GroupedFamilyComposition.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.GroupedFamilyComposition.classicalSigmaDecidableEq
variable {Primary Body Group : Type*} [Fintype Primary] [Fintype Body] [Fintype Group]
  (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
  {Input Middle : Group → Type*}
  [∀ group, Fintype (Input group)] [∀ group, Fintype (Middle group)]
  (preprocess : ∀ group, (Input group → ℝ) →ₗ[ℝ] (Middle group → ℝ))
  (channels : ∀ group, (Middle group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h92 (pattern : Group → TruncatedArity order)
    (input : ((group : Group) → Input group) → ℝ) :
    patternKernel primary body order (fun group => (channels group).comp (preprocess group)) pattern input =
      patternKernel primary body order channels pattern (DependentTensorChannel.apply preprocess input) := by
  apply Subtype.ext
  change canonicalize _ _ _ _
    (DependentTensorChannel.apply
      (componentChannel primary body order (fun group => (channels group).comp (preprocess group)) pattern) input) =
    canonicalize _ _ _ _ (DependentTensorChannel.apply
      (componentChannel primary body order channels pattern) (DependentTensorChannel.apply preprocess input))
  congr 1
  have hchannel : componentChannel primary body order
      (fun group => (channels group).comp (preprocess group)) pattern =
      fun group => (componentChannel primary body order channels pattern group).comp (preprocess group) := rfl
  rw [hchannel, _p2mH81]
open _root_.P2M9e1cfc64 renaming h92 → _p2mH92
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h91 (pattern : Group → TruncatedArity order)
    (input : ((group : Group) → Input group) → ℝ) :
    patternFamily primary body order (fun group => (channels group).comp (preprocess group)) pattern input =
      patternFamily primary body order channels pattern (DependentTensorChannel.apply preprocess input) := by
  unfold patternFamily
  split_ifs
  · rw [_p2mH92]
  · rfl
open _root_.P2M9e1cfc64 renaming h91 → _p2mH91
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h93 (input : ((group : Group) → Input group) → ℝ) :
    response primary body order (fun group => (channels group).comp (preprocess group)) input =
      response primary body order channels (DependentTensorChannel.apply preprocess input) := by
  unfold response
  simp_rw [_p2mH91]
open _root_.P2M9e1cfc64 renaming h93 → _p2mH93
end
open _root_.P2M9e1cfc64 renaming h91 → _p2mH91
open _root_.P2M9e1cfc64 renaming h92 → _p2mH92
open _root_.P2M9e1cfc64 renaming h93 → _p2mH93
end CurrentAFT.GroupedFamilyComposition
open _root_.P2M9e1cfc64 renaming h91 → _p2mH91
open _root_.P2M9e1cfc64 renaming h92 → _p2mH92
open _root_.P2M9e1cfc64 renaming h93 → _p2mH93
end
open _root_.P2M9e1cfc64 renaming h92 → _p2mH92
open _root_.P2M9e1cfc64 renaming h93 → _p2mH93
open _root_.P2M9e1cfc64 renaming h91 → _p2mH91
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
theorem _root_.P2M9e1cfc64.h43 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    response order horder queue selection tagged layout kernel =
      GroupedFamilyTensor.response (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order
        (ActualRootGroupedChannel.channel order horder queue selection tagged) (jointInput selection tagged layout kernel) := rfl
open _root_.P2M9e1cfc64 renaming h43 → _p2mH43
end
open _root_.P2M9e1cfc64 renaming h43 → _p2mH43
end CurrentAFT.ActualRootResponse
open _root_.P2M9e1cfc64 renaming h43 → _p2mH43
end
open _root_.P2M9e1cfc64 renaming h43 → _p2mH43
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
theorem _root_.P2M9e1cfc64.h30 {State : Type*} [Fintype State] (reference : FiniteDist State)
    (test : State → ℝ) (bound : ℝ) (hbound : 1 ≤ bound)
    (point : State) (hatom : 1 ≤ bound * reference.weight point) :
    |test point| ≤ bound * Real.sqrt (reference.l2Sq test) := by
  have he : 0 ≤ reference.l2Sq test := FiniteDist.l2Sq_nonneg _ _
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
open _root_.P2M9e1cfc64 renaming h30 → _p2mH30
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h24 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (bound : ℝ) (hbound : 1 ≤ bound)
    (hp : ∀ color, 1 ≤ bound * primary.weight color) (hb : ∀ color, 1 ≤ bound * body.weight color)
    {r s : ℕ} (kernel : DensityKernel (Primary := Primary) (Body := Body) r s)
    (colors : Fin r → Primary) (centers : Fin s → Body) :
    |kernel colors centers| ≤ bound ^ (r + s) * blockL2 primary body kernel := by
  let reference := (FiniteDist.independent (fun _ : Fin r => primary)).prod
    (FiniteDist.independent (fun _ : Fin s => body))
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
  exact _p2mH30 reference (fun pair => kernel pair.1 pair.2) _
    (one_le_pow₀ hbound) (colors, centers) hatom
open _root_.P2M9e1cfc64 renaming h24 → _p2mH24
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h25 (security r s : ℕ)
    (kernel : DensityKernel (Primary := ActualControls.Palette security) (Body := SafePalette security) r s)
    (colors : Fin r → ActualControls.Palette security) (centers : Fin s → SafePalette security) :
    |kernel colors centers| ≤ (2 * (Parameters.modulus security : ℝ)) ^ (r + s) *
      blockL2 (primaryLaw security) (bodyReference security) kernel := by
  have hq := FirstResponse.modulus_pos security
  have hq1 : (1 : ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.one_le
  apply _p2mH24 _ _ _ (by linarith)
  · intro color
    have h := primaryProfile_atom_lower security color
    have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * (Parameters.modulus security : ℝ))
    simpa only [primaryLaw, mul_one_div_cancel (by positivity : (2 * (Parameters.modulus security : ℝ)) ≠ 0)] using hm
  · intro color
    have hm := mul_le_mul_of_nonneg_left (bodyReference_lower security color)
      (by positivity : 0 ≤ 2 * (Parameters.modulus security : ℝ))
    simpa only [mul_one_div_cancel (by positivity : (2 * (Parameters.modulus security : ℝ)) ≠ 0)] using hm
open _root_.P2M9e1cfc64 renaming h25 → _p2mH25
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h27 (security : ℕ) : (1 : ℝ) ≤ Parameters.dimension security := by
  have h := (Parameters.dimension_bounds security).1
  have hp := pow_pos (Parameters.base_pos security) 160
  exact_mod_cast (show 1 ≤ Parameters.dimension security by omega)
open _root_.P2M9e1cfc64 renaming h27 → _p2mH27
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h28 (security : ℕ) :
    1 ≤ (Parameters.dimension security : ℝ) * primaryFactor security := by
  have hd := _p2mH27 security
  have hl : (Parameters.legCount security : ℝ) ≤ Parameters.dimension security := by
    exact_mod_cast (show Parameters.legCount security ≤ Parameters.dimension security by
      unfold Parameters.dimension; omega)
  have hlpos : (0 : ℝ) < Parameters.legCount security := by
    have h : 0 < Parameters.legCount security := by
      unfold Parameters.legCount Parameters.scale
      exact pow_pos (pow_pos (Parameters.base_pos security) _) _
    exact_mod_cast h
  have hsqrt : Real.sqrt (Parameters.legCount security : ℝ) ≤ Parameters.dimension security := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith
    · nlinarith
  unfold primaryFactor
  rw [← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.mpr hlpos), one_mul]
  exact hsqrt
open _root_.P2M9e1cfc64 renaming h28 → _p2mH28
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h26 (security : ℕ) :
    1 ≤ (Parameters.dimension security : ℝ) * bodyFactor security := by
  have hd := _p2mH27 security
  have hp : (0 : ℝ) < ordinaryPool security := by exact_mod_cast ordinaryPool_pos security
  have hpool : (ordinaryPool security : ℝ) ≤ Parameters.dimension security := by
    exact_mod_cast (show ordinaryPool security ≤ Parameters.dimension security by
      unfold ordinaryPool Parameters.dimension; omega)
  have hr : (1 : ℝ) ≤ radius security := by
    apply Real.one_le_rpow
    · exact_mod_cast (Parameters.base_ge_two security).trans' (by omega)
    · norm_num
  have hsqrt : Real.sqrt (ordinaryPool security : ℝ) ≤ Parameters.dimension security := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith
    · nlinarith
  unfold bodyFactor
  rw [← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.mpr hp), one_mul]
  exact hsqrt.trans (le_mul_of_one_le_right (by linarith) hr)
open _root_.P2M9e1cfc64 renaming h26 → _p2mH26
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h29 (security order : ℕ) (family : Family security order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → ActualControls.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(family arity).val colors centers| ≤
      (2 * (Parameters.modulus security : ℝ) * Parameters.dimension security)^order *
        LocalRaisingBounds.coefficientNorm security order family := by
  have hd := _p2mH27 security
  have hp := (RaisingPatternBudget.primaryFactor_pos security).le
  have hb := (RaisingPatternBudget.bodyFactor_pos security).le
  have hn := familyNorm_nonneg (primaryLaw security) (bodyReference security) order _ _ hp hb family
  have hweight : 1 ≤ (Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
      gradeWeight (primaryFactor security) (bodyFactor security) arity.val.1.val arity.val.2.val := by
    have h := one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (_p2mH28 security) (n := arity.val.1.val))
      (one_le_pow₀ (_p2mH26 security) (n := arity.val.2.val))
    simpa only [gradeWeight, mul_pow, pow_add, mul_mul_mul_comm] using h
  have hsingle : gradeWeight (primaryFactor security) (bodyFactor security) arity.val.1.val arity.val.2.val *
      blockL2 (primaryLaw security) (bodyReference security) (family arity).val ≤
        LocalRaisingBounds.coefficientNorm security order family := by
    unfold LocalRaisingBounds.coefficientNorm familyNorm
    exact Finset.single_le_sum (fun index _ => mul_nonneg
      (gradeWeight_nonneg _ _ hp hb index.val.1.val index.val.2.val)
      (blockL2_nonneg (primaryLaw security) (bodyReference security) (family index).val))
      (Finset.mem_univ arity)
  have hblock : blockL2 (primaryLaw security) (bodyReference security) (family arity).val ≤
      (Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
        LocalRaisingBounds.coefficientNorm security order family := by
    have hfirst := mul_le_mul_of_nonneg_right hweight (blockL2_nonneg (primaryLaw security) (bodyReference security) (family arity).val)
    have hsecond := mul_le_mul_of_nonneg_left hsingle
      (pow_nonneg (by linarith : (0 : ℝ) ≤ Parameters.dimension security) (arity.val.1.val + arity.val.2.val))
    nlinarith only [hfirst, hsecond]
  have hq : (1 : ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.one_le
  have hlarge : (1 : ℝ) ≤ 2 * (Parameters.modulus security : ℝ) * Parameters.dimension security := by nlinarith
  calc
    _ ≤ (2 * (Parameters.modulus security : ℝ))^(arity.val.1.val + arity.val.2.val) *
        blockL2 (primaryLaw security) (bodyReference security) (family arity).val := _p2mH25 security _ _ _ _ _
    _ ≤ (2 * (Parameters.modulus security : ℝ))^(arity.val.1.val + arity.val.2.val) *
        ((Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
          LocalRaisingBounds.coefficientNorm security order family) := mul_le_mul_of_nonneg_left hblock (by positivity)
    _ = (2 * (Parameters.modulus security : ℝ) * Parameters.dimension security)^(arity.val.1.val + arity.val.2.val) *
        LocalRaisingBounds.coefficientNorm security order family := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlarge arity.property) hn
open _root_.P2M9e1cfc64 renaming h29 → _p2mH29
end
open _root_.P2M9e1cfc64 renaming h24 → _p2mH24
open _root_.P2M9e1cfc64 renaming h25 → _p2mH25
open _root_.P2M9e1cfc64 renaming h26 → _p2mH26
open _root_.P2M9e1cfc64 renaming h27 → _p2mH27
open _root_.P2M9e1cfc64 renaming h28 → _p2mH28
open _root_.P2M9e1cfc64 renaming h29 → _p2mH29
open _root_.P2M9e1cfc64 renaming h30 → _p2mH30
end CurrentAFT.ActualCoordinateBounds
open _root_.P2M9e1cfc64 renaming h24 → _p2mH24
open _root_.P2M9e1cfc64 renaming h25 → _p2mH25
open _root_.P2M9e1cfc64 renaming h26 → _p2mH26
open _root_.P2M9e1cfc64 renaming h27 → _p2mH27
open _root_.P2M9e1cfc64 renaming h28 → _p2mH28
open _root_.P2M9e1cfc64 renaming h29 → _p2mH29
open _root_.P2M9e1cfc64 renaming h30 → _p2mH30
end
open _root_.P2M9e1cfc64 renaming h27 → _p2mH27
open _root_.P2M9e1cfc64 renaming h30 → _p2mH30
open _root_.P2M9e1cfc64 renaming h24 → _p2mH24
open _root_.P2M9e1cfc64 renaming h25 → _p2mH25
open _root_.P2M9e1cfc64 renaming h26 → _p2mH26
open _root_.P2M9e1cfc64 renaming h28 → _p2mH28
open _root_.P2M9e1cfc64 renaming h29 → _p2mH29
section
namespace CurrentAFT.ActualPublicLegCharge
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram InwardAnchor
open scoped BigOperators Classical Fin.NatCast
noncomputable section
attribute [local instance] _root_.CurrentAFT.ActualPublicLegCharge.chargeFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualPublicLegCharge.chargeModulusNeZero
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h35 (security : ℕ) (shift : ℤ) (color : Palette security)
    (hlower : 0 ≤ (color.val : ℤ) + shift)
    (hupper : (color.val : ℤ) + shift < Parameters.modulus security) :
    ((shiftEquiv security shift color).val : ℤ) = (color.val : ℤ) + shift := by
  let output : Palette security := ⟨((color.val : ℤ) + shift).toNat, by omega⟩
  have houtput : (output.val : ℤ) = (color.val : ℤ) + shift := by dsimp [output]; omega
  have hemb (point : Palette security) : (ZMod.finEquiv (Parameters.modulus security)) point =
      (point.val : ZMod (Parameters.modulus security)) := finEquiv_natCast _ point
  have hequal : shiftEquiv security shift color = output := by
    apply (ZMod.finEquiv (Parameters.modulus security)).injective
    change (ZMod.finEquiv (Parameters.modulus security))
      ((ZMod.finEquiv (Parameters.modulus security)).symm
        ((ZMod.finEquiv (Parameters.modulus security)) color + (shift : ZMod (Parameters.modulus security)))) = _
    rw [RingEquiv.apply_symm_apply, hemb, hemb]
    have hcast := congrArg (fun value : ℤ => (value : ZMod (Parameters.modulus security))) houtput
    simpa only [Int.cast_natCast, Int.cast_add] using hcast.symm
  rw [hequal, houtput]
open _root_.P2M9e1cfc64 renaming h35 → _p2mH35
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h32 (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) :
    (markedPoint security primary scalar seed).val =
      ((Parameters.modulus security : ℤ) - 1 - primary.val + publicShift security primary seed - scalar.val).toNat := by
  have hs := integerPoint_safe security primary seed.coin seed.anchorIndex (-scalar.val)
    (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)
  have hp := point_value security primary seed.coin seed.anchorIndex (-scalar.val)
    (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)
  have hblur := abs_le.mp (blur_bound security seed)
  have hmargin : (Parameters.safeMargin security : ℤ) = 3 * (Parameters.sourceCutoff security : ℤ) := by
    rw [Parameters.safeMargin]
    push_cast
    ring
  have hcut := InwardAnchor.sourceCutoff_pos security
  have hvalue := _p2mH35 security (seed.blur.1.val - seed.blur.2.val)
    (point security primary seed.coin seed.anchorIndex (-scalar.val)
      (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar))
    (by rw [hp]; omega) (by rw [hp]; omega)
  change (shiftEquiv security (seed.blur.1.val - seed.blur.2.val) _).val = _
  apply Int.ofNat_inj.mp
  rw [hvalue, hp]
  have hequal : integerPoint security primary seed.coin seed.anchorIndex (-scalar.val) +
      (seed.blur.1.val - seed.blur.2.val) =
      (Parameters.modulus security : ℤ) - 1 - primary.val + publicShift security primary seed - scalar.val := by
    unfold integerPoint publicShift signedOffset
    ring
  rw [← hequal, Int.toNat_of_nonneg]
  omega
open _root_.P2M9e1cfc64 renaming h32 → _p2mH32
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h31 (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) (pair : Palette security × Palette security) :
    (markedLaw security primary scalar seed).weight pair =
      if (primary, markedPoint security primary scalar seed) = pair then 1 else 0 := by
  simp [markedLaw, FiniteDist.map_weight, FiniteDist.uniform_weight]
open _root_.P2M9e1cfc64 renaming h31 → _p2mH31
end
open _root_.P2M9e1cfc64 renaming h31 → _p2mH31
open _root_.P2M9e1cfc64 renaming h32 → _p2mH32
open _root_.P2M9e1cfc64 renaming h35 → _p2mH35
end CurrentAFT.ActualPublicLegCharge
open _root_.P2M9e1cfc64 renaming h31 → _p2mH31
open _root_.P2M9e1cfc64 renaming h32 → _p2mH32
open _root_.P2M9e1cfc64 renaming h35 → _p2mH35
end
open _root_.P2M9e1cfc64 renaming h32 → _p2mH32
open _root_.P2M9e1cfc64 renaming h35 → _p2mH35
open _root_.P2M9e1cfc64 renaming h31 → _p2mH31
section
namespace CurrentAFT.ActualPublicLegCharge
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram InwardAnchor
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.ActualPublicLegCharge.disintegrationFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualPublicLegCharge.disintegrationAnchorWidthNeZero
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
set_option maxRecDepth 8192
private theorem _root_.P2M9e1cfc64.h551 {First Second Output : Type*} [Fintype First] [Fintype Second] [Fintype Output]
    (first : FiniteDist First) (second : FiniteDist Second) (kernel : First → Second → FiniteDist Output) :
    first.mix (fun left => second.mix (kernel left)) =
      second.mix (fun right => first.mix (fun left => kernel left right)) := by
  ext output
  simp only [FiniteDist.mix_weight, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro left _
  ring
open _root_.P2M9e1cfc64 renaming h551 → _p2mH551
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h34 (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (coin : Bool) (blur : BlurSeed security) :
    (FiniteDist.uniform (InwardAnchor.Index security)).mix (fun index =>
      markedLaw security primary scalar ⟨true, coin, index, blur⟩) =
      ((fixedCoinLaw security primary coin (-scalar.val)
        (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)).map
          (shiftEquiv security (blur.1.val - blur.2.val))).map (fun companion => (primary, companion)) := by
  ext pair
  simp only [FiniteDist.mix_weight, _p2mH31, fixedCoinLaw, FiniteDist.map_map, FiniteDist.map_weight,
    markedPoint, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro index _
  split_ifs <;> rfl
open _root_.P2M9e1cfc64 renaming h34 → _p2mH34
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h33 (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security) :
    (FiniteDist.uniform Bool).mix (fun coin =>
      (FiniteDist.uniform (InwardAnchor.Index security)).mix (fun index =>
        (publicBlurLaw security).mix (fun blur => markedLaw security primary scalar ⟨true, coin, index, blur⟩))) =
          markedPairAt security primary scalar := by
  have hswap (coin : Bool) := _p2mH551 (FiniteDist.uniform (InwardAnchor.Index security)) (publicBlurLaw security)
    (fun index blur => markedLaw security primary scalar ⟨true, coin, index, blur⟩)
  simp_rw [hswap]
  rw [_p2mH551 (FiniteDist.uniform Bool) (publicBlurLaw security)]
  simp_rw [_p2mH34]
  unfold markedPairAt markedCompanionAt shiftedAnchorLaw
  rw [FiniteDist.map_mix]
  apply congrArg (publicBlurLaw security).mix
  funext blur
  rw [FiniteDist.map_mix, FiniteDist.map_mix]
open _root_.P2M9e1cfc64 renaming h33 → _p2mH33
end
open _root_.P2M9e1cfc64 renaming h33 → _p2mH33
open _root_.P2M9e1cfc64 renaming h34 → _p2mH34
open _root_.P2M9e1cfc64 renaming h551 → _p2mH551
end CurrentAFT.ActualPublicLegCharge
open _root_.P2M9e1cfc64 renaming h33 → _p2mH33
open _root_.P2M9e1cfc64 renaming h34 → _p2mH34
open _root_.P2M9e1cfc64 renaming h551 → _p2mH551
end
open _root_.P2M9e1cfc64 renaming h33 → _p2mH33
open _root_.P2M9e1cfc64 renaming h34 → _p2mH34
section
namespace CurrentAFT.RootLocalDenominators
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst IndependentPairedReference
  PositiveFirstCoefficient ActualBlockFock RootTaggedSelected RootReferenceExpectation
  RootBackgroundPolynomial RootIndependentBackground BodyRootAverages BackgroundPolynomialEvaluation
  BackgroundEndpointLaw CycleRootExpansion ControlCoordinates GradedControlAlgebra GradedControlNorm
  LocalCoefficientFamily LocalRaisingBounds NormalizedLocalPolynomial
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootLocalDenominators.classicalFinDecidableEq
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h485 (security : ℕ) (queue : ℤ) :
    RootTaggedLocal.meanLaw security .free queue = BackgroundCertificates.convolvedCenterLaw security := by
  unfold RootTaggedLocal.meanLaw RootTaggedLocal.shiftedLaw UniformBodyProfiles.preRootLaw
  rw [_p2mH484, _p2mH46]
open _root_.P2M9e1cfc64 renaming h485 → _p2mH485
end
open _root_.P2M9e1cfc64 renaming h485 → _p2mH485
end CurrentAFT.RootLocalDenominators
open _root_.P2M9e1cfc64 renaming h485 → _p2mH485
end
open _root_.P2M9e1cfc64 renaming h485 → _p2mH485
section
namespace CurrentAFT.ActualRootPhysicalResponse
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  CycleRootExpansion ControlCoordinates GradedControlAlgebra LocalCoefficientFamily
  RootLocalDenominators FinitePolynomialTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualRootPhysicalResponse.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootPhysicalResponse.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootPhysicalResponse.classicalProdDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootPhysicalResponse.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
private theorem _root_.P2M9e1cfc64.h552 : (Finset.univ : Finset (Fin 1)).toList = [0] := by
  apply Finset.toList_eq_singleton_iff.mpr
  ext index
  rw [Fin.eq_zero index]
  simp
open _root_.P2M9e1cfc64 renaming h552 → _p2mH552
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h38 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin r) :
    PairedRootProjection.projector selection tagged (.inl (.inl index)) =
      RootPrimaryGroupedChannel.projector security (ActualRootGroupedChannel.primaryFlags selection tagged index) := rfl
open _root_.P2M9e1cfc64 renaming h38 → _p2mH38
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h37 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin s) :
    PairedRootProjection.projector selection tagged (.inl (.inr index)) =
      RootOrdinaryGroupedChannel.projector security (ActualRootGroupedChannel.ordinaryFlag selection tagged index) := by
  change RootCoordinateProjection.sequence (rootReference security)
    ((Finset.univ : Finset (Fin 1)).toList.map (fun slot =>
      (slot, decide (rootEmbedding selection tagged ⟨.inl (.inr index), slot⟩ ∈ tagged)))) = _
  simp only [_p2mH552, List.map_cons, List.map_nil, RootCoordinateProjection.sequence,
    LinearMap.comp_id]
  rfl
open _root_.P2M9e1cfc64 renaming h37 → _p2mH37
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h36 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : HitKept selection tagged) :
    PairedRootProjection.projector selection tagged (.inr index) =
      RootCoordinateProjection.center (rootReference security) (0 : Fin 1) := by
  change RootCoordinateProjection.sequence (rootReference security)
    ((Finset.univ : Finset (Fin 1)).toList.map (fun slot =>
      (slot, decide (rootEmbedding selection tagged ⟨.inr index, slot⟩ ∈ tagged)))) = _
  simp only [_p2mH552, List.map_cons, List.map_nil, RootCoordinateProjection.sequence,
    LinearMap.comp_id]
  have hroot : rootEmbedding selection tagged ⟨.inr index, (0 : Fin 1)⟩ = index.val.val := rfl
  rw [hroot]
  simp only [index.property, decide_true, RootCoordinateProjection.coordinate, if_true]
open _root_.P2M9e1cfc64 renaming h36 → _p2mH36
end
open _root_.P2M9e1cfc64 renaming h36 → _p2mH36
open _root_.P2M9e1cfc64 renaming h37 → _p2mH37
open _root_.P2M9e1cfc64 renaming h38 → _p2mH38
open _root_.P2M9e1cfc64 renaming h552 → _p2mH552
end CurrentAFT.ActualRootPhysicalResponse
open _root_.P2M9e1cfc64 renaming h36 → _p2mH36
open _root_.P2M9e1cfc64 renaming h37 → _p2mH37
open _root_.P2M9e1cfc64 renaming h38 → _p2mH38
open _root_.P2M9e1cfc64 renaming h552 → _p2mH552
end
open _root_.P2M9e1cfc64 renaming h38 → _p2mH38
open _root_.P2M9e1cfc64 renaming h36 → _p2mH36
open _root_.P2M9e1cfc64 renaming h37 → _p2mH37
section
namespace CurrentAFT.ActualRootProjectionData
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  CycleRootExpansion ControlCoordinates GradedControlAlgebra LocalCoefficientFamily
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualRootProjectionData.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootProjectionData.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootProjectionData.classicalProdDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootProjectionData.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h42 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : BlockIndex security) (constant : ℝ) :
    RootUnselectedBlockChannel.channel security order horder queue block (fun _ => constant) = 0 := by
  have hconstant : (fun _ : Root security => constant) = constant • (fun _ => (1 : ℝ)) := by
    funext root
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  rw [hconstant, map_smul]
  suffices h : RootUnselectedBlockChannel.channel security order horder queue block (fun _ => 1) = 0 by
    rw [h, smul_zero]
  have hsingle (role : UniformBodyProfiles.BodyRole) (shift : ℤ) :
      RootUnselectedChannels.singletonChannel security order horder role shift (fun _ => 1) = 0 := by
    change RootTaggedFamilies.rootFamilyLinear security order horder role shift (fun _ => 1) * _ = 0
    rw [_p2mH531, zero_mul]
  rcases block with leg | single
  · change (RootTaggedFamilies.rootFamilyLinear security order horder .attachment 0 (fun _ => 1) +
      RootLegCoefficientLinear.rootHigherLinear security order (fun _ => 1)) * _ = 0
    rw [_p2mH531]
    change (0 + RootLegCoefficientLinear.higherFamilyLinear security order
      (RootTaggedLegHigher.massLinear security (fun _ => 1))) * _ = 0
    rw [_p2mH532, map_zero, add_zero, zero_mul]
  · rcases single with center | point
    · exact hsingle .free 0
    · exact hsingle .queue queue
open _root_.P2M9e1cfc64 renaming h42 → _p2mH42
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h41 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : BlockIndex security) (score : RootUnselectedGrouped.Input security → ℝ) :
    RootUnselectedGrouped.channel security order horder queue block
      (RootCoordinateProjection.center (rootReference security) (0 : Fin 1) score) =
        RootUnselectedGrouped.channel security order horder queue block score := by
  have haverage : RootUnselectedGrouped.extractLinear security
      (RootCoordinateProjection.average (rootReference security) (0 : Fin 1) score) =
      fun _ => (rootReference security).expectation (RootUnselectedGrouped.extractLinear security score) := by
    funext root
    change (rootReference security).expectation (fun other =>
      score (Function.update (fun _ : Fin 1 => root) 0 other, ())) = _
    simp only [Function.update_eq_const_of_subsingleton]
    rfl
  change RootUnselectedBlockChannel.channel security order horder queue block
    (RootUnselectedGrouped.extractLinear security (score - RootCoordinateProjection.average (rootReference security) (0 : Fin 1) score)) = _
  rw [map_sub, haverage, map_sub, _p2mH42, sub_zero]
  rfl
open _root_.P2M9e1cfc64 renaming h41 → _p2mH41
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h39 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (group : ActiveGroup selection tagged) :
    ActualRootGroupedChannel.channel order horder queue selection tagged group =
      (unprojectedChannel order horder queue selection tagged group).comp
        (PairedRootProjection.projector selection tagged group) := by
  rcases group with (primary | ordinary) | kept
  · rw [_p2mH38]
    rfl
  · rw [_p2mH37]
    rfl
  · rw [_p2mH36]
    apply LinearMap.ext
    intro score
    exact (_p2mH41 security order horder queue kept.val.val score).symm
open _root_.P2M9e1cfc64 renaming h39 → _p2mH39
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h40 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    ActualRootResponse.response order horder queue selection tagged layout kernel =
      GroupedFamilyTensor.response (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order
        (unprojectedChannel order horder queue selection tagged) (jointInput selection tagged layout kernel) := by
  rw [_p2mH43]
  have hchannels : ActualRootGroupedChannel.channel order horder queue selection tagged = fun group =>
      (unprojectedChannel order horder queue selection tagged group).comp
        (PairedRootProjection.projector selection tagged group) :=
    funext (_p2mH39 order horder queue selection tagged)
  rw [hchannels, _p2mH93, _p2mH135]
open _root_.P2M9e1cfc64 renaming h40 → _p2mH40
end
open _root_.P2M9e1cfc64 renaming h39 → _p2mH39
open _root_.P2M9e1cfc64 renaming h40 → _p2mH40
open _root_.P2M9e1cfc64 renaming h41 → _p2mH41
open _root_.P2M9e1cfc64 renaming h42 → _p2mH42
end CurrentAFT.ActualRootProjectionData
open _root_.P2M9e1cfc64 renaming h39 → _p2mH39
open _root_.P2M9e1cfc64 renaming h40 → _p2mH40
open _root_.P2M9e1cfc64 renaming h41 → _p2mH41
open _root_.P2M9e1cfc64 renaming h42 → _p2mH42
end
open _root_.P2M9e1cfc64 renaming h42 → _p2mH42
open _root_.P2M9e1cfc64 renaming h40 → _p2mH40
open _root_.P2M9e1cfc64 renaming h39 → _p2mH39
open _root_.P2M9e1cfc64 renaming h41 → _p2mH41
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
theorem _root_.P2M9e1cfc64.h48 {State : Type*} [Fintype State]
    (law : FiniteDist State) (value : State → ℝ) (bound : ℝ)
    (hbound : ∀ state, |value state| ≤ bound) : |law.expectation value| ≤ bound := by
  unfold FiniteDist.expectation
  calc
    _ ≤ ∑ state, |law.weight state * value state| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ state, law.weight state * bound := by
      apply Finset.sum_le_sum
      intro state _
      rw [abs_mul, abs_of_nonneg (law.nonneg state)]
      exact mul_le_mul_of_nonneg_left (hbound state) (law.nonneg state)
    _ = bound := by rw [← Finset.sum_mul, law.sum_one, one_mul]
open _root_.P2M9e1cfc64 renaming h48 → _p2mH48
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
end
open _root_.P2M9e1cfc64 renaming h48 → _p2mH48
end CurrentAFT.CalibrationCoordinateError
open _root_.P2M9e1cfc64 renaming h48 → _p2mH48
end
open _root_.P2M9e1cfc64 renaming h48 → _p2mH48
section
namespace CurrentAFT.CalibrationRectanglePadding
open AFT RationalNumerics
open scoped BigOperators
variable {Small Large : Type*}
section
variable [Fintype Small] [Fintype Large]
variable (encode : Small ↪ Large) (decode : Large → Option Small)
variable (hdecode : ∀ point small, decode point = some small ↔ point = encode small)
include encode hdecode
set_option maxRecDepth 8192
omit [Fintype Small] [Fintype Large] in
theorem _root_.P2M9e1cfc64.h49 (point : Small) : decode (encode point) = some point :=
  (hdecode _ _).mpr rfl
open _root_.P2M9e1cfc64 renaming h49 → _p2mH49
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h50 {Scalar : Type*} [AddCommMonoid Scalar] (table : Small → Scalar) :
    (∑ point, extend decode table point) = ∑ point, table point := by
  have hsubset : Finset.univ.map encode ⊆ (Finset.univ : Finset Large) := Finset.subset_univ _
  have hsum := Finset.sum_subset hsubset (f := extend decode table) (by
    intro point _ hnot
    have hn : decode point = none := by
      cases hd : decode point with
      | none => rfl
      | some small =>
        have hp := (hdecode point small).mp hd
        subst point
        exact False.elim (hnot (Finset.mem_map.mpr ⟨small, Finset.mem_univ _, rfl⟩))
    simp only [extend, hn, Option.elim_none])
  rw [← hsum, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro point _
  simp only [extend, _p2mH49 encode decode hdecode, Option.elim_some]
open _root_.P2M9e1cfc64 renaming h50 → _p2mH50
end
open _root_.P2M9e1cfc64 renaming h49 → _p2mH49
open _root_.P2M9e1cfc64 renaming h50 → _p2mH50
end CurrentAFT.CalibrationRectanglePadding
open _root_.P2M9e1cfc64 renaming h49 → _p2mH49
open _root_.P2M9e1cfc64 renaming h50 → _p2mH50
end
open _root_.P2M9e1cfc64 renaming h49 → _p2mH49
open _root_.P2M9e1cfc64 renaming h50 → _p2mH50
section
namespace CurrentAFT.WindowGaussianSampler
open AFT GaussianSource RationalNumerics DiffuseProfiles
open scoped BigOperators Classical
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h549 (security : ℕ) : 0 < squaredWidth security := by
  unfold squaredWidth
  positivity
open _root_.P2M9e1cfc64 renaming h549 → _p2mH549
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h550 (security : ℕ) :
    (squaredWidth security : ℝ) = (Parameters.sourceWidth security : ℝ)^2 := by
  unfold squaredWidth Parameters.sourceWidth Parameters.base
  push_cast
  rfl
open _root_.P2M9e1cfc64 renaming h550 → _p2mH550
noncomputable section
end
end CurrentAFT.WindowGaussianSampler
open _root_.P2M9e1cfc64 renaming h549 → _p2mH549
open _root_.P2M9e1cfc64 renaming h550 → _p2mH550
end
open _root_.P2M9e1cfc64 renaming h550 → _p2mH550
open _root_.P2M9e1cfc64 renaming h549 → _p2mH549
section
namespace CurrentAFT.TensorPublicProjection
open AFT JointTaggedPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.TensorPublicProjection.finDecEq
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h541 {Index Color : Type*} [Fintype Index] [Fintype Color]
    (first second : DecidableEq Index) (law : Index → FiniteDist Color) (value : (Index → Color) → ℝ) :
    @FiniteDist.expectation (Index → Color) (@Pi.instFintype Index (fun _ => Color) first _ (fun _ => inferInstance))
      (@FiniteDist.independent Color Index _ _ first law) value =
    @FiniteDist.expectation (Index → Color) (@Pi.instFintype Index (fun _ => Color) second _ (fun _ => inferInstance))
      (@FiniteDist.independent Color Index _ _ second law) value := by
  cases Subsingleton.elim first second
  rfl
open _root_.P2M9e1cfc64 renaming h541 → _p2mH541
section Generic
variable {Index Primary Body : Type*} [Fintype Index] [Fintype Primary] [Fintype Body]
  [DecidableEq Index]
end Generic
section TwoPools
variable {Primary Body Public : Type*} [Fintype Primary] [Fintype Body] [Fintype Public]
end TwoPools
end
open _root_.P2M9e1cfc64 renaming h541 → _p2mH541
end CurrentAFT.TensorPublicProjection
open _root_.P2M9e1cfc64 renaming h541 → _p2mH541
end
open _root_.P2M9e1cfc64 renaming h541 → _p2mH541
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.joint
end AFT.FiniteDist.joint
namespace AFT.MixedKernel
end AFT.MixedKernel
section
namespace CurrentAFT.CyclePatternProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h75 {body order : ℕ} (sites : Fin order → Fin body) : (touched sites).card ≤ 2 * order := by
  apply (Finset.card_union_le _ _).trans
  have hcurrent := Finset.card_image_le (s := (Finset.univ : Finset (Fin order))) (f := sites)
  have hprevious := Finset.card_image_le (s := (Finset.univ : Finset (Fin order)))
    (f := fun slot => (finRotate body).symm (sites slot))
  simp only [Finset.card_univ, Fintype.card_fin] at hcurrent hprevious
  omega
open _root_.P2M9e1cfc64 renaming h75 → _p2mH75
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h71 {body order : ℕ} (security cutoff bits : ℕ)
    (sites : Fin order → Fin body) (test : (Fin order → ℤ) → ℚ) :
    gaussianEvaluate security cutoff bits sites test =
      evaluate sites (windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits)
        (fun point : Window cutoff => point.val) test := by
  exact congrArg (fun enumeration : Fintype (Window cutoff) =>
    @evaluate (Window cutoff) ℤ enumeration inferInstance body order sites
      (windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits)
      (fun point => point.val) test) (Subsingleton.elim _ _)
open _root_.P2M9e1cfc64 renaming h71 → _p2mH71
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h74 {Scalar Group : Type*} [Fintype Scalar] [AddGroup Group]
    {body order : ℕ} (sites : Fin order → Fin body) (source : FiniteDist Scalar)
    (value : Scalar → Group) (test : (Fin order → Group) → ℝ) :
    (FiniteDist.independent (fun _ : Fin body => source)).expectation (fun latent =>
      test (fun slot => value (latent (sites slot)) - value (latent ((finRotate body).symm (sites slot))))) =
      (FiniteDist.independent (fun _ : touched sites => source)).expectation (fun latent => test (roots sites value latent)) := by
  let embedding : touched sites ↪ Fin body := ⟨Subtype.val, Subtype.val_injective⟩
  have h := _p2mH0
    (fun _ : Fin body => source) embedding (fun latent => test (roots sites value latent))
  apply Eq.trans (_p2mH541
    (inferInstance : DecidableEq (Fin body)) (Classical.decEq _) (fun _ => source) _)
  apply Eq.trans h
  exact _p2mH541 (Classical.decEq _)
    (inferInstance : DecidableEq (touched sites)) (fun _ => source) _
open _root_.P2M9e1cfc64 renaming h74 → _p2mH74
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h68 {Scalar Group : Type*} [Fintype Scalar] [AddGroup Group]
    {body order : ℕ} (sites : Fin order → Fin body) (source : FiniteDist Scalar)
    (weight : Scalar → ℚ) (hweight : ∀ scalar, (weight scalar : ℝ) = source.weight scalar)
    (value : Scalar → Group) (test : (Fin order → Group) → ℚ) :
    (evaluate sites weight value test : ℝ) =
      (FiniteDist.independent (fun _ : touched sites => source)).expectation
        (fun latent => (test (roots sites value latent) : ℝ)) := by
  simp only [evaluate, Rat.cast_sum, Rat.cast_mul, Rat.cast_prod, hweight,
    FiniteDist.expectation, FiniteDist.independent]
open _root_.P2M9e1cfc64 renaming h68 → _p2mH68
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h69 {Scalar Group : Type*} [Fintype Scalar] [AddGroup Group]
    {body order : ℕ} (sites : Fin order → Fin body) (source : FiniteDist Scalar)
    (weight : Scalar → ℚ) (hweight : ∀ scalar, (weight scalar : ℝ) = source.weight scalar)
    (value : Scalar → Group) (test : (Fin order → Group) → ℚ) :
    (evaluate sites weight value test : ℝ) =
      (FiniteDist.independent (fun _ : Fin body => source)).expectation (fun latent =>
        (test (fun slot => value (latent (sites slot)) - value (latent ((finRotate body).symm (sites slot)))) : ℝ)) := by
  exact (_p2mH68 sites source weight hweight value test).trans
    (_p2mH74 sites source value (fun input => (test input : ℝ))).symm
open _root_.P2M9e1cfc64 renaming h69 → _p2mH69
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h73 {body order : ℕ} (security cutoff bits : ℕ)
    (sites : Fin order → Fin body) (test : (Fin order → ℤ) → ℚ) :
    (gaussianEvaluate security cutoff bits sites test : ℝ) =
      (FiniteDist.independent (fun _ : Fin body => windowApproxLaw
        (WindowGaussianSampler.squaredWidth security) cutoff bits)).expectation (fun latent =>
          (test (fun slot => (latent (sites slot)).val - (latent ((finRotate body).symm (sites slot))).val) : ℝ)) :=
by
  rw [_p2mH71]
  exact _p2mH69 sites _ _ (fun _ => rfl) _ test
open _root_.P2M9e1cfc64 renaming h73 → _p2mH73
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h70 {State : Type*} [Fintype State] (first second : FiniteDist State)
    (test : State → ℝ) (bound : ℝ) (htest : ∀ state, |test state| ≤ bound) :
    |first.expectation test - second.expectation test| ≤
      bound * ∑ state, |first.weight state - second.weight state| := by
  unfold FiniteDist.expectation
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
open _root_.P2M9e1cfc64 renaming h70 → _p2mH70
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h72 {body order : ℕ} (security cutoff bits : ℕ)
    (sites : Fin order → Fin body) (test : (Fin order → ℤ) → ℚ) (bound : ℝ)
    (hbound : 0 ≤ bound) (htest : ∀ roots, |(test roots : ℝ)| ≤ bound) :
    |(gaussianEvaluate security cutoff bits sites test : ℝ) -
      (FiniteDist.independent (fun _ : Fin body => windowGaussian (Parameters.sourceWidth security) cutoff)).expectation
        (fun latent => (test (fun slot => (latent (sites slot)).val -
          (latent ((finRotate body).symm (sites slot))).val) : ℝ))| ≤
      (2 * order : ℕ) * bound / (2 : ℝ)^bits := by
  rw [_p2mH71]
  let first := windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits
  let second := windowGaussian (Parameters.sourceWidth security) cutoff
  have hscalar : (∑ point, |first.weight point - second.weight point|) ≤ 1 / (2 : ℝ)^bits :=
    _p2mH14 _ _ _ _ (_p2mH549 security)
      (_p2mH550 security).symm
  have hproduct := FiniteDist.l1_independent_le (fun _ : touched sites => first) (fun _ => second)
  have hlocal : (∑ latent,
      |(FiniteDist.independent (fun _ : touched sites => first)).weight latent -
        (FiniteDist.independent (fun _ : touched sites => second)).weight latent|) ≤
      (2 * order : ℕ) / (2 : ℝ)^bits := by
    apply hproduct.trans
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    calc
      _ ≤ ((touched sites).card : ℝ) * (1 / (2 : ℝ)^bits) :=
        mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg _)
      _ ≤ (2 * order : ℕ) * (1 / (2 : ℝ)^bits) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (_p2mH75 sites)) (by positivity)
      _ = _ := by ring
  have hprogram := _p2mH68 sites first
    (windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits) (fun _ => rfl)
    (fun point : Window cutoff => point.val) test
  have htrue := _p2mH74 sites second (fun point : Window cutoff => point.val)
    (fun input => (test input : ℝ))
  calc
    _ = |(FiniteDist.independent (fun _ : touched sites => first)).expectation
        (fun latent => (test (roots sites (fun point : Window cutoff => point.val) latent) : ℝ)) -
      (FiniteDist.independent (fun _ : touched sites => second)).expectation
        (fun latent => (test (roots sites (fun point : Window cutoff => point.val) latent) : ℝ))| :=
      congrArg abs (congrArg₂ (· - ·) hprogram htrue)
    _ ≤ _ := (_p2mH70 _ _
      (fun latent => (test (roots sites (fun point : Window cutoff => point.val) latent) : ℝ))
      bound (fun _ => htest _)).trans ((mul_le_mul_of_nonneg_left hlocal hbound).trans_eq (by ring))
open _root_.P2M9e1cfc64 renaming h72 → _p2mH72
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h67 {body order : ℕ} (security bits : ℕ) (sites : Fin order → Fin body)
    (test : (Fin order → ℤ) → ℚ) (bound : ℝ) (hbound : 0 ≤ bound)
    (htest : ∀ roots, |(test roots : ℝ)| ≤ bound) :
    |(gaussianEvaluate security (edgeCutoff security) bits sites test : ℝ) -
      (FiniteDist.independent (fun _ : Fin body => edgeLaw security)).expectation (fun latent =>
        (test (fun slot => (latent (sites slot)).val - (latent ((finRotate body).symm (sites slot))).val) : ℝ))| ≤
      (2 * order : ℕ) * bound / (2 : ℝ)^bits :=
  _p2mH72 security _ bits sites test bound hbound htest
open _root_.P2M9e1cfc64 renaming h67 → _p2mH67
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h65 (security cutoff bits body order : ℕ) (hroom : order ≤ body)
    (test : (Fin order ↪ Fin body) → (Fin order → ℤ) → ℚ) :
    (averagedEvaluate security cutoff bits body order test : ℝ) =
      (CycleSelections.selectionLaw body order hroom).expectation
        (fun sites => (gaussianEvaluate security cutoff bits sites (test sites) : ℝ)) := by
  have henumeration (first second : Fintype (Fin order ↪ Fin body)) (value : (Fin order ↪ Fin body) → ℝ) :
      ((@Fintype.card (Fin order ↪ Fin body) first : ℝ)⁻¹ * ∑ state ∈ @Finset.univ (Fin order ↪ Fin body) first, value state) =
        ((@Fintype.card (Fin order ↪ Fin body) second : ℝ)⁻¹ * ∑ state ∈ @Finset.univ (Fin order ↪ Fin body) second, value state) := by
    cases Subsingleton.elim first second
    rfl
  unfold averagedEvaluate
  simp only [Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum,
    CycleSelections.selectionLaw, FiniteDist.expectation, FiniteDist.uniform_weight, ← Finset.mul_sum]
  exact henumeration (selectionFintype body order) (inferInstance : Fintype (Fin order ↪ Fin body))
    (fun sites => (gaussianEvaluate security cutoff bits sites (test sites) : ℝ))
open _root_.P2M9e1cfc64 renaming h65 → _p2mH65
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h66 (security bits body order : ℕ) (hroom : order ≤ body)
    (test : (Fin order ↪ Fin body) → (Fin order → ℤ) → ℚ) (bound : ℝ)
    (hbound : 0 ≤ bound) (htest : ∀ sites roots, |(test sites roots : ℝ)| ≤ bound) :
    |(averagedEvaluate security (edgeCutoff security) bits body order test : ℝ) -
      (CycleSelections.selectionLaw body order hroom).expectation (fun sites =>
        (FiniteDist.independent (fun _ : Fin body => edgeLaw security)).expectation (fun latent =>
          (test sites (fun slot => (latent (sites slot)).val -
            (latent ((finRotate body).symm (sites slot))).val) : ℝ)))| ≤
      (2 * order : ℕ) * bound / (2 : ℝ)^bits := by
  rw [_p2mH65 security (edgeCutoff security) bits body order hroom]
  rw [← FiniteDist.expectation_sub]
  exact _p2mH2 _ _ _ (fun sites =>
    _p2mH67 security bits sites (test sites) bound hbound (htest sites))
open _root_.P2M9e1cfc64 renaming h66 → _p2mH66
end
open _root_.P2M9e1cfc64 renaming h65 → _p2mH65
open _root_.P2M9e1cfc64 renaming h66 → _p2mH66
open _root_.P2M9e1cfc64 renaming h67 → _p2mH67
open _root_.P2M9e1cfc64 renaming h68 → _p2mH68
open _root_.P2M9e1cfc64 renaming h69 → _p2mH69
open _root_.P2M9e1cfc64 renaming h70 → _p2mH70
open _root_.P2M9e1cfc64 renaming h72 → _p2mH72
open _root_.P2M9e1cfc64 renaming h73 → _p2mH73
open _root_.P2M9e1cfc64 renaming h74 → _p2mH74
end CurrentAFT.CyclePatternProgram
open _root_.P2M9e1cfc64 renaming h65 → _p2mH65
open _root_.P2M9e1cfc64 renaming h66 → _p2mH66
open _root_.P2M9e1cfc64 renaming h67 → _p2mH67
open _root_.P2M9e1cfc64 renaming h68 → _p2mH68
open _root_.P2M9e1cfc64 renaming h69 → _p2mH69
open _root_.P2M9e1cfc64 renaming h70 → _p2mH70
open _root_.P2M9e1cfc64 renaming h71 → _p2mH71
open _root_.P2M9e1cfc64 renaming h72 → _p2mH72
open _root_.P2M9e1cfc64 renaming h73 → _p2mH73
open _root_.P2M9e1cfc64 renaming h74 → _p2mH74
open _root_.P2M9e1cfc64 renaming h75 → _p2mH75
end
open _root_.P2M9e1cfc64 renaming h65 → _p2mH65
open _root_.P2M9e1cfc64 renaming h71 → _p2mH71
open _root_.P2M9e1cfc64 renaming h70 → _p2mH70
open _root_.P2M9e1cfc64 renaming h68 → _p2mH68
open _root_.P2M9e1cfc64 renaming h75 → _p2mH75
open _root_.P2M9e1cfc64 renaming h72 → _p2mH72
open _root_.P2M9e1cfc64 renaming h66 → _p2mH66
open _root_.P2M9e1cfc64 renaming h69 → _p2mH69
open _root_.P2M9e1cfc64 renaming h73 → _p2mH73
open _root_.P2M9e1cfc64 renaming h67 → _p2mH67
open _root_.P2M9e1cfc64 renaming h74 → _p2mH74
section
namespace CurrentAFT.LocalDiffuseProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles LocalReferenceEnergy
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h117 (security colors width cutoff bits primary : ℕ)
    (source : ℤ) (first second : ℕ) :
    evaluate security colors width cutoff bits primary source first second =
      ∑ left : Window cutoff, ∑ right : Window cutoff,
        windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits left *
          windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits right *
            blurEntry colors width primary source first second (left.val-right.val) := by
  let term (left right : Window cutoff) : ℚ :=
    windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits left *
      windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits right *
        blurEntry colors width primary source first second (left.val-right.val)
  change (∑ left : Fin (2*cutoff+1), ∑ right : Fin (2*cutoff+1),
    term (FiniteConvolutionProgram.windowIndexEquiv cutoff left)
      (FiniteConvolutionProgram.windowIndexEquiv cutoff right)) =
    ∑ left : Window cutoff, ∑ right : Window cutoff, term left right
  trans ∑ left : Fin (2*cutoff+1), ∑ right : Window cutoff,
    term (FiniteConvolutionProgram.windowIndexEquiv cutoff left) right
  · exact Finset.sum_congr rfl (fun left _ =>
      (FiniteConvolutionProgram.windowIndexEquiv cutoff).sum_comp (term _))
  · exact (FiniteConvolutionProgram.windowIndexEquiv cutoff).sum_comp
      (fun left => ∑ right : Window cutoff, term left right)
open _root_.P2M9e1cfc64 renaming h117 → _p2mH117
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h114 (security : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) (blur : BlurSeed security) (coin : Bool) :
    (coinEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
      (blur.1.val - blur.2.val) coin first.val second.val : ℝ) =
      (FirstHistogram.diffuseSeedPair security (InwardAnchor.positiveDirection security primary coin) (blur, source)).weight
        (first, second) := by
  rw [FirstHistogram.diffuseSeedPair_weight]
  unfold coinEntry
  rw [_p2mH18]
  rfl
open _root_.P2M9e1cfc64 renaming h114 → _p2mH114
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h113 (colors width primary : ℕ) (source : ℤ) (first second : ℕ) (blur : ℤ) :
    |(blurEntry colors width primary source first second blur : ℝ)| ≤ 1 := by
  have htrue := _p2mH17 colors 1
    ((if direction colors primary true then (width : ℤ) else -2 * (width : ℤ) + 1) + blur) source width first second
  have hfalse := _p2mH17 colors 1
    ((if direction colors primary false then (width : ℤ) else -2 * (width : ℤ) + 1) + blur) source width first second
  unfold blurEntry
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
  change (|(coinEntry colors width primary source blur true first second : ℝ)| +
    |(coinEntry colors width primary source blur false first second : ℝ)|) / 2 ≤ 1
  change |(coinEntry colors width primary source blur true first second : ℝ)| ≤ 1 at htrue
  change |(coinEntry colors width primary source blur false first second : ℝ)| ≤ 1 at hfalse
  linarith only [htrue, hfalse]
open _root_.P2M9e1cfc64 renaming h113 → _p2mH113
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h116 (security colors width cutoff bits primary : ℕ) (source : ℤ) (first second : ℕ) :
    (evaluate security colors width cutoff bits primary source first second : ℝ) =
      ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits).prod
        (windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits)).expectation
          (fun blur => (blurEntry colors width primary source first second (blur.1.val - blur.2.val) : ℝ)) := by
  simp only [_p2mH117, Rat.cast_sum, Rat.cast_mul, FiniteDist.expectation,
    FiniteDist.prod_weight, Fintype.sum_prod_type, windowApproxLaw]
open _root_.P2M9e1cfc64 renaming h116 → _p2mH116
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h119 (security : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    (publicBlurLaw security).expectation (fun blur =>
      (blurEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
        first.val second.val (blur.1.val - blur.2.val) : ℝ)) =
      (diffusePairAt security primary source).weight (first, second) := by
  unfold diffusePairAt
  change _ = (FiniteDist.uniform Bool).expectation (fun coin => (publicBlurLaw security).expectation
    (fun blur => (FirstHistogram.diffuseSeedPair security
      (InwardAnchor.positiveDirection security primary coin) (blur, source)).weight (first, second)))
  conv_rhs => rw [FiniteDist.expectation_comm]
  apply congrArg (FiniteDist.expectation _)
  funext blur
  simp only [blurEntry, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, _p2mH114,
    FiniteDist.expectation, Fintype.sum_bool, FiniteDist.uniform_weight, Fintype.card_bool, Nat.cast_ofNat]
  ring
open _root_.P2M9e1cfc64 renaming h119 → _p2mH119
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h118 (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    |(evaluate security (Parameters.modulus security) (Parameters.anchorWidth security) (edgeCutoff security)
      bits primary.val source.val first.val second.val : ℝ) -
        (diffusePairAt security primary source).weight (first, second)| ≤ 2 / (2 : ℝ)^bits := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits
  have hscalar : (∑ point, |approximate.weight point - (edgeLaw security).weight point|) ≤ 1 / (2 : ℝ)^bits :=
    _p2mH14 _ _ _ _ (_p2mH549 security)
      (_p2mH550 security).symm
  have hprod := FiniteDist.l1_prod_le approximate (edgeLaw security) approximate (edgeLaw security)
  have hl1 : (∑ blur, |(approximate.prod approximate).weight blur - (publicBlurLaw security).weight blur|) ≤
      2 / (2 : ℝ)^bits := by
    apply hprod.trans
    exact (add_le_add hscalar hscalar).trans_eq (by ring)
  calc
    _ = |(approximate.prod approximate).expectation (fun blur =>
        (blurEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
          first.val second.val (blur.1.val - blur.2.val) : ℝ)) -
      (publicBlurLaw security).expectation (fun blur =>
        (blurEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
          first.val second.val (blur.1.val - blur.2.val) : ℝ))| :=
        congrArg abs (congrArg₂ (· - ·) (_p2mH116 _ _ _ _ _ _ _ _ _)
          (_p2mH119 security primary first second source).symm)
    _ ≤ _ := (_p2mH70 _ _ _ 1
      (fun blur => _p2mH113 _ _ _ _ _ _ _)).trans (by simpa only [one_mul] using hl1)
open _root_.P2M9e1cfc64 renaming h118 → _p2mH118
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h115 (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    |(current security bits primary.val source.val first.val second.val : ℝ) -
      (diffusePairAt security primary source).weight (first, second)| ≤ 2 / (2 : ℝ)^bits := by
  have hwidth : (security + 2)^48 = Parameters.anchorWidth security := by
    simp only [DiffuseProfiles.anchorWidth_eq, Parameters.base]
  have hcutoff : ((security + 2)^2 - 1) / 2 = edgeCutoff security := by
    simp only [edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  unfold current
  rw [PublicParameterProgram.modulus_value, hwidth, hcutoff]
  exact _p2mH118 security bits primary first second source
open _root_.P2M9e1cfc64 renaming h115 → _p2mH115
end
open _root_.P2M9e1cfc64 renaming h113 → _p2mH113
open _root_.P2M9e1cfc64 renaming h114 → _p2mH114
open _root_.P2M9e1cfc64 renaming h115 → _p2mH115
open _root_.P2M9e1cfc64 renaming h116 → _p2mH116
open _root_.P2M9e1cfc64 renaming h117 → _p2mH117
open _root_.P2M9e1cfc64 renaming h118 → _p2mH118
open _root_.P2M9e1cfc64 renaming h119 → _p2mH119
end CurrentAFT.LocalDiffuseProgram
open _root_.P2M9e1cfc64 renaming h113 → _p2mH113
open _root_.P2M9e1cfc64 renaming h114 → _p2mH114
open _root_.P2M9e1cfc64 renaming h115 → _p2mH115
open _root_.P2M9e1cfc64 renaming h116 → _p2mH116
open _root_.P2M9e1cfc64 renaming h117 → _p2mH117
open _root_.P2M9e1cfc64 renaming h118 → _p2mH118
open _root_.P2M9e1cfc64 renaming h119 → _p2mH119
end
open _root_.P2M9e1cfc64 renaming h117 → _p2mH117
open _root_.P2M9e1cfc64 renaming h119 → _p2mH119
open _root_.P2M9e1cfc64 renaming h114 → _p2mH114
open _root_.P2M9e1cfc64 renaming h116 → _p2mH116
open _root_.P2M9e1cfc64 renaming h118 → _p2mH118
open _root_.P2M9e1cfc64 renaming h113 → _p2mH113
open _root_.P2M9e1cfc64 renaming h115 → _p2mH115
section
namespace CurrentAFT.LocalMarkedProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles LocalReferenceEnergy ActualPublicLegCharge
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.LocalMarkedProgram.markedIndexNonempty
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h125 (security colors width cutoff bits primary : ℕ)
    (source : ℤ) (first second : ℕ) :
    evaluate security colors width cutoff bits primary source first second =
      ∑ left : Window cutoff, ∑ right : Window cutoff,
        windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits left *
          windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits right *
            blurEntry colors width primary source first second (left.val-right.val) := by
  let term (left right : Window cutoff) : ℚ :=
    windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits left *
      windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits right *
        blurEntry colors width primary source first second (left.val-right.val)
  change (∑ left : Fin (2*cutoff+1), ∑ right : Fin (2*cutoff+1),
    term (FiniteConvolutionProgram.windowIndexEquiv cutoff left)
      (FiniteConvolutionProgram.windowIndexEquiv cutoff right)) =
    ∑ left : Window cutoff, ∑ right : Window cutoff, term left right
  trans ∑ left : Fin (2*cutoff+1), ∑ right : Window cutoff,
    term (FiniteConvolutionProgram.windowIndexEquiv cutoff left) right
  · exact Finset.sum_congr rfl (fun left _ =>
      (FiniteConvolutionProgram.windowIndexEquiv cutoff).sum_comp (term _))
  · exact (FiniteConvolutionProgram.windowIndexEquiv cutoff).sum_comp
      (fun left => ∑ right : Window cutoff, term left right)
open _root_.P2M9e1cfc64 renaming h125 → _p2mH125
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h128 (colors width primary : ℕ) (source blur : ℤ) (coin : Bool)
    (index : Fin width) (first second : ℕ) :
    |(pointEntry colors width primary source blur coin index first second : ℝ)| ≤ 1 := by
  unfold pointEntry
  split_ifs <;> norm_num
open _root_.P2M9e1cfc64 renaming h128 → _p2mH128
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h121 (colors width primary : ℕ) (source blur : ℤ) (coin : Bool) (first second : ℕ) :
    |(coinEntry colors width primary source blur coin first second : ℝ)| ≤ 1 := by
  by_cases hw : width = 0
  · simp [coinEntry, hw]
  have hwR : (width : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hw
  have hsum : |∑ index : Fin width, (pointEntry colors width primary source blur coin index first second : ℝ)| ≤ width := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _index : Fin width, (1 : ℝ) := Finset.sum_le_sum (fun index _ => _p2mH128 _ _ _ _ _ _ index _ _)
      _ = _ := by simp
  simp only [coinEntry, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum, abs_mul,
    abs_inv, abs_of_nonneg (Nat.cast_nonneg width : (0 : ℝ) ≤ width)]
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))).trans_eq
    (inv_mul_cancel₀ hwR)
open _root_.P2M9e1cfc64 renaming h121 → _p2mH121
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h120 (colors width primary : ℕ) (source : ℤ) (first second : ℕ) (blur : ℤ) :
    |(blurEntry colors width primary source first second blur : ℝ)| ≤ 1 := by
  have ht := _p2mH121 colors width primary source blur true first second
  have hf := _p2mH121 colors width primary source blur false first second
  unfold blurEntry
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
  linarith only [ht, hf]
open _root_.P2M9e1cfc64 renaming h120 → _p2mH120
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h129 (security : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) (blur : BlurSeed security) (coin : Bool)
    (index : InwardAnchor.Index security) :
    (pointEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
      (blur.1.val - blur.2.val) coin index first.val second.val : ℝ) =
      (markedLaw security primary source ⟨true, coin, index, blur⟩).weight (first, second) := by
  rw [_p2mH31]
  have hvalue : companionValue (Parameters.modulus security) (Parameters.anchorWidth security)
      primary.val source.val (blur.1.val - blur.2.val) coin index =
      (Parameters.modulus security : ℤ) - 1 - primary.val +
        publicShift security primary ⟨true, coin, index, blur⟩ - source.val := by
    unfold companionValue publicShift signedOffset InwardAnchor.offset
    change (Parameters.modulus security : ℤ) - 1 - primary.val +
      (if InwardAnchor.positiveDirection security primary coin then
        (Parameters.anchorWidth security : ℤ) + index.val else -((Parameters.anchorWidth security : ℤ) + index.val)) +
      (blur.1.val - blur.2.val) - source.val = _
    ring
  have hpoint : (companionValue (Parameters.modulus security) (Parameters.anchorWidth security)
      primary.val source.val (blur.1.val - blur.2.val) coin index).toNat =
      (markedPoint security primary source ⟨true, coin, index, blur⟩).val := by
    rw [_p2mH32, hvalue]
  simp only [pointEntry, hpoint, Prod.mk.injEq, Fin.ext_iff]
  split_ifs <;> norm_num
open _root_.P2M9e1cfc64 renaming h129 → _p2mH129
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h122 (security : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) (blur : BlurSeed security) (coin : Bool) :
    (coinEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
      (blur.1.val - blur.2.val) coin first.val second.val : ℝ) =
      (FiniteDist.uniform (InwardAnchor.Index security)).expectation (fun index =>
        (markedLaw security primary source ⟨true, coin, index, blur⟩).weight (first, second)) := by
  simp only [coinEntry, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum,
    _p2mH129, FiniteDist.expectation, FiniteDist.uniform_weight, Fintype.card_fin,
    Finset.mul_sum]
open _root_.P2M9e1cfc64 renaming h122 → _p2mH122
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h124 (security colors width cutoff bits primary : ℕ) (source : ℤ) (first second : ℕ) :
    (evaluate security colors width cutoff bits primary source first second : ℝ) =
      ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits).prod
        (windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits)).expectation
          (fun blur => (blurEntry colors width primary source first second (blur.1.val - blur.2.val) : ℝ)) := by
  simp only [_p2mH125, Rat.cast_sum, Rat.cast_mul, FiniteDist.expectation,
    FiniteDist.prod_weight, Fintype.sum_prod_type, windowApproxLaw]
open _root_.P2M9e1cfc64 renaming h124 → _p2mH124
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h127 (security : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    (publicBlurLaw security).expectation (fun blur =>
      (blurEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
        first.val second.val (blur.1.val - blur.2.val) : ℝ)) =
      (markedPairAt security primary source).weight (first, second) := by
  rw [← _p2mH33]
  change _ = (FiniteDist.uniform Bool).expectation (fun coin =>
    (FiniteDist.uniform (InwardAnchor.Index security)).expectation (fun index =>
      (publicBlurLaw security).expectation (fun blur =>
        (markedLaw security primary source ⟨true, coin, index, blur⟩).weight (first, second))))
  simp_rw [FiniteDist.expectation_comm (FiniteDist.uniform (InwardAnchor.Index security)) (publicBlurLaw security)]
  rw [FiniteDist.expectation_comm (FiniteDist.uniform Bool) (publicBlurLaw security)]
  apply congrArg (FiniteDist.expectation (publicBlurLaw security))
  funext blur
  simp only [blurEntry, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, _p2mH122,
    FiniteDist.expectation, Fintype.sum_bool, FiniteDist.uniform_weight, Fintype.card_bool, Nat.cast_ofNat]
  ring
open _root_.P2M9e1cfc64 renaming h127 → _p2mH127
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h126 (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    |(evaluate security (Parameters.modulus security) (Parameters.anchorWidth security) (edgeCutoff security)
      bits primary.val source.val first.val second.val : ℝ) -
        (markedPairAt security primary source).weight (first, second)| ≤ 2 / (2 : ℝ)^bits := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits
  have hscalar : (∑ point, |approximate.weight point - (edgeLaw security).weight point|) ≤ 1 / (2 : ℝ)^bits :=
    _p2mH14 _ _ _ _ (_p2mH549 security)
      (_p2mH550 security).symm
  have hprod := FiniteDist.l1_prod_le approximate (edgeLaw security) approximate (edgeLaw security)
  have hl1 : (∑ blur, |(approximate.prod approximate).weight blur - (publicBlurLaw security).weight blur|) ≤
      2 / (2 : ℝ)^bits := hprod.trans ((add_le_add hscalar hscalar).trans_eq (by ring))
  calc
    _ = |(approximate.prod approximate).expectation (fun blur =>
        (blurEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
          first.val second.val (blur.1.val - blur.2.val) : ℝ)) -
      (publicBlurLaw security).expectation (fun blur =>
        (blurEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
          first.val second.val (blur.1.val - blur.2.val) : ℝ))| :=
        congrArg abs (congrArg₂ (· - ·) (_p2mH124 _ _ _ _ _ _ _ _ _)
          (_p2mH127 security primary first second source).symm)
    _ ≤ _ := (_p2mH70 _ _ _ 1
      (fun blur => _p2mH120 _ _ _ _ _ _ _)).trans (by simpa only [one_mul] using hl1)
open _root_.P2M9e1cfc64 renaming h126 → _p2mH126
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h123 (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    |(current security bits primary.val source.val first.val second.val : ℝ) -
      (markedPairAt security primary source).weight (first, second)| ≤ 2 / (2 : ℝ)^bits := by
  have hwidth : (security + 2)^48 = Parameters.anchorWidth security := by
    simp only [DiffuseProfiles.anchorWidth_eq, Parameters.base]
  have hcutoff : ((security + 2)^2 - 1) / 2 = edgeCutoff security := by
    simp only [edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  unfold current
  rw [PublicParameterProgram.modulus_value, hwidth, hcutoff]
  exact _p2mH126 security bits primary first second source
open _root_.P2M9e1cfc64 renaming h123 → _p2mH123
end
open _root_.P2M9e1cfc64 renaming h120 → _p2mH120
open _root_.P2M9e1cfc64 renaming h121 → _p2mH121
open _root_.P2M9e1cfc64 renaming h122 → _p2mH122
open _root_.P2M9e1cfc64 renaming h123 → _p2mH123
open _root_.P2M9e1cfc64 renaming h124 → _p2mH124
open _root_.P2M9e1cfc64 renaming h125 → _p2mH125
open _root_.P2M9e1cfc64 renaming h126 → _p2mH126
open _root_.P2M9e1cfc64 renaming h127 → _p2mH127
open _root_.P2M9e1cfc64 renaming h128 → _p2mH128
open _root_.P2M9e1cfc64 renaming h129 → _p2mH129
end CurrentAFT.LocalMarkedProgram
open _root_.P2M9e1cfc64 renaming h120 → _p2mH120
open _root_.P2M9e1cfc64 renaming h121 → _p2mH121
open _root_.P2M9e1cfc64 renaming h122 → _p2mH122
open _root_.P2M9e1cfc64 renaming h123 → _p2mH123
open _root_.P2M9e1cfc64 renaming h124 → _p2mH124
open _root_.P2M9e1cfc64 renaming h125 → _p2mH125
open _root_.P2M9e1cfc64 renaming h126 → _p2mH126
open _root_.P2M9e1cfc64 renaming h127 → _p2mH127
open _root_.P2M9e1cfc64 renaming h128 → _p2mH128
open _root_.P2M9e1cfc64 renaming h129 → _p2mH129
end
open _root_.P2M9e1cfc64 renaming h126 → _p2mH126
open _root_.P2M9e1cfc64 renaming h125 → _p2mH125
open _root_.P2M9e1cfc64 renaming h120 → _p2mH120
open _root_.P2M9e1cfc64 renaming h124 → _p2mH124
open _root_.P2M9e1cfc64 renaming h121 → _p2mH121
open _root_.P2M9e1cfc64 renaming h129 → _p2mH129
open _root_.P2M9e1cfc64 renaming h122 → _p2mH122
open _root_.P2M9e1cfc64 renaming h128 → _p2mH128
open _root_.P2M9e1cfc64 renaming h127 → _p2mH127
open _root_.P2M9e1cfc64 renaming h123 → _p2mH123
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
theorem _root_.P2M9e1cfc64.h130 (security bits : ℕ) :
    |(activationApprox security bits : ℝ) - DiffuseProfiles.activation security| ≤ (1/2:ℝ) * (1 / (2:ℝ)^bits) := by
  let law := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits
  have hsum : (∑ point, |law.weight point - (scalarLaw security).weight point|) ≤ 1 / (2:ℝ)^bits :=
    _p2mH14 _ _ _ _ (_p2mH549 security)
      (_p2mH550 security).symm
  have hatom := Finset.single_le_sum (f := fun point => |law.weight point - (scalarLaw security).weight point|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ (windowZero (Parameters.sourceCutoff security - 1)))
  have heq : (activationApprox security bits : ℝ) = (1/2:ℝ)*law.weight (windowZero _) := by
    simp only [activationApprox, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    rfl
  rw [heq]
  unfold DiffuseProfiles.activation
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  exact mul_le_mul_of_nonneg_left (hatom.trans hsum) (by norm_num)
open _root_.P2M9e1cfc64 renaming h130 → _p2mH130
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h131 (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    |(current security bits primary.val source.val first.val second.val : ℝ) -
      (pairAt security primary source).weight (first, second)| ≤ 3 / (2:ℝ)^bits := by
  let rate : ℝ := activationApprox security bits
  let diffuse : ℝ := LocalDiffuseProgram.current security bits primary.val source.val first.val second.val
  let marked : ℝ := LocalMarkedProgram.current security bits primary.val source.val first.val second.val
  let trueDiffuse := (diffusePairAt security primary source).weight (first, second)
  let trueMarked := (markedPairAt security primary source).weight (first, second)
  have hr := activationApprox_bounds security bits
  have hrate : 0 ≤ rate ∧ rate ≤ 1/2 := hr
  have hcompl : 0 ≤ 1-rate := by linarith only [hrate.2]
  have hd := _p2mH115 security bits primary first second source
  have hm := _p2mH123 security bits primary first second source
  have ha := _p2mH130 security bits
  have hdiffuse : |trueDiffuse| ≤ 1 := by
    rw [abs_of_nonneg ((diffusePairAt security primary source).nonneg _)]
    exact (diffusePairAt security primary source).atom_le_one _
  have hmarked : |trueMarked| ≤ 1 := by
    rw [abs_of_nonneg ((markedPairAt security primary source).nonneg _)]
    exact (markedPairAt security primary source).atom_le_one _
  have hgap : |trueMarked - trueDiffuse| ≤ 2 := by
    exact (abs_sub _ _).trans (by linarith only [hdiffuse, hmarked])
  unfold current
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
  change |(1-rate)*diffuse + rate*marked -
    ((1-DiffuseProfiles.activation security)*trueDiffuse + DiffuseProfiles.activation security*trueMarked)| ≤ _
  calc
    _ = |(1-rate)*(diffuse-trueDiffuse) + rate*(marked-trueMarked) +
        (rate-DiffuseProfiles.activation security)*(trueMarked-trueDiffuse)| := by congr 1; ring
    _ ≤ |(1-rate)*(diffuse-trueDiffuse)| + |rate*(marked-trueMarked)| +
        |(rate-DiffuseProfiles.activation security)*(trueMarked-trueDiffuse)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = (1-rate) * |diffuse-trueDiffuse| + rate * |marked-trueMarked| +
        |rate-DiffuseProfiles.activation security| * |trueMarked-trueDiffuse| := by
      rw [abs_mul, abs_of_nonneg hcompl, abs_mul, abs_of_nonneg hrate.1, abs_mul]
    _ ≤ (1-rate)*(2/(2:ℝ)^bits) + rate*(2/(2:ℝ)^bits) + ((1/2:ℝ)*(1/(2:ℝ)^bits))*2 :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hd hcompl)
        (mul_le_mul_of_nonneg_left hm hrate.1))
        (mul_le_mul ha hgap (abs_nonneg _) (by positivity))
    _ = _ := by ring
open _root_.P2M9e1cfc64 renaming h131 → _p2mH131
end
open _root_.P2M9e1cfc64 renaming h130 → _p2mH130
open _root_.P2M9e1cfc64 renaming h131 → _p2mH131
end CurrentAFT.LocalPairProgram
open _root_.P2M9e1cfc64 renaming h130 → _p2mH130
open _root_.P2M9e1cfc64 renaming h131 → _p2mH131
end
open _root_.P2M9e1cfc64 renaming h131 → _p2mH131
open _root_.P2M9e1cfc64 renaming h130 → _p2mH130
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
theorem _root_.P2M9e1cfc64.h381 (security bits : ℕ) (primary output : FirstHistogram.Palette security) :
    |(anchor security bits primary.val output.val : ℝ) -
      (InwardAnchor.smoothedAnchorLaw security primary).weight output| ≤ 1 / (2 : ℝ)^bits := by
  rw [anchor_cast]
  have hl1 := _p2mH14 (WindowGaussianSampler.squaredWidth security)
    (Parameters.sourceWidth security) (Parameters.sourceCutoff security - 1) bits
    (_p2mH549 security) (_p2mH550 security).symm
  have h := _p2mH70
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits)
    (scalarLaw security)
    (fun scalar => (InwardAnchor.shiftedAnchorLaw security primary scalar.val
      (InwardAnchor.scalar_bound security scalar)).weight output) 1 (fun scalar => by
      rw [abs_of_nonneg ((InwardAnchor.shiftedAnchorLaw security primary scalar.val
        (InwardAnchor.scalar_bound security scalar)).nonneg output)]
      exact (InwardAnchor.shiftedAnchorLaw security primary scalar.val
        (InwardAnchor.scalar_bound security scalar)).atom_le_one output)
  exact h.trans (by simpa only [one_mul,scalarLaw] using hl1)
open _root_.P2M9e1cfc64 renaming h381 → _p2mH381
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h393 (security bits : ℕ) :
    (∑ seed, |(approximateSeedLaw security bits).weight seed - (actualSeedLaw security).weight seed|) ≤
      3 / (2 : ℝ)^bits := by
  have he := _p2mH14 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (edgeCutoff security) bits (_p2mH549 security)
    (_p2mH550 security).symm
  have hs := _p2mH14 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security - 1) bits (_p2mH549 security)
    (_p2mH550 security).symm
  have hp := FiniteDist.l1_prod_le
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits)
    (edgeLaw security)
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits) (edgeLaw security)
  have hall := FiniteDist.l1_prod_le
    ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits).prod
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits))
    ((edgeLaw security).prod (edgeLaw security))
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits)
    (scalarLaw security)
  exact hall.trans ((add_le_add (hp.trans (add_le_add he he)) hs).trans_eq (by ring))
open _root_.P2M9e1cfc64 renaming h393 → _p2mH393
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h383 (security bits : ℕ) (includeScalar : Bool) (output : FirstHistogram.Palette security) :
    |(body security bits includeScalar output.val : ℝ) - (bodyLaw security includeScalar).weight output| ≤
      3 / (2 : ℝ)^bits := by
  rw [body_cast]
  exact (_p2mH70 (approximateSeedLaw security bits)
    (actualSeedLaw security) (fun seed => ((safeLaw security).map
      (shiftEquiv security (actualBlur security seed + if includeScalar then actualSecond security seed else 0))).weight output)
      1 (fun seed => by
        rw [abs_of_nonneg (FiniteDist.nonneg _ _)]
        exact FiniteDist.atom_le_one _ _)).trans (by simpa only [one_mul] using _p2mH393 security bits)
open _root_.P2M9e1cfc64 renaming h383 → _p2mH383
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h387 (colors width output : ℕ) (blur second : ℤ) :
    |(diffuseKernel colors width blur second output : ℝ)| ≤ 1 := by
  have hp := _p2mH19 colors 1
    ((width : ℤ) + blur) second width output
  have hm := _p2mH19 colors 1
    (-2 * (width : ℤ) + 1 + blur) second width output
  simp only [diffuseKernel, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (by linarith only [hp, hm])
open _root_.P2M9e1cfc64 renaming h387 → _p2mH387
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h388 (security bits : ℕ) (output : FirstHistogram.Palette security) :
    |(diffuse security bits output.val : ℝ) - diffuseMean security output| ≤ 3 / (2 : ℝ)^bits := by
  rw [diffuse_cast]
  change |fairProfile security (approximateSeedLaw security bits) output -
    fairProfile security (actualSeedLaw security) output| ≤ _
  rw [fairProfile_expectation, fairProfile_expectation]
  exact (_p2mH70 _ _ _ 1
    (fun seed => _p2mH387 _ _ _ _ _)).trans
      (by simpa only [one_mul] using _p2mH393 security bits)
open _root_.P2M9e1cfc64 renaming h388 → _p2mH388
set_option maxRecDepth 8192
private theorem _root_.P2M9e1cfc64.h559
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
open _root_.P2M9e1cfc64 renaming h559 → _p2mH559
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h390 (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ))) :
    |(primaryRaw security bits output.val : ℝ) - primaryProfile security output| ≤
      64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let rate : ℝ := LocalPairProgram.activationApprox security bits
  have hepsilon : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have hb := FirstResponse.base_pos security
  have hrate := LocalPairProgram.activationApprox_bounds security bits
  have hrateError : |rate - DiffuseProfiles.activation security| ≤ epsilon / 2 := by
    exact (_p2mH130 security bits).trans_eq (by dsimp only [epsilon]; ring)
  have hrateLower : 1 / (8 * (Parameters.base security : ℝ)) ≤ rate := by
    have ha := FirstResponse.activation_lower_simple security
    have hfrac : 1 / (8 * (Parameters.base security : ℝ)) = (1 / (4 * (Parameters.base security : ℝ))) / 2 := by ring
    rw [hfrac]
    linarith [(abs_le.mp hrateError).1, hprecision]
  have hlegsPos : (0 : ℝ) < Parameters.legCount security := by
    exact_mod_cast (show 0 < Parameters.legCount security by
      rw [Parameters.legCount_eq]; exact pow_pos (Parameters.base_pos security) _)
  have hlegsOne : (1 : ℝ) ≤ Parameters.legCount security := by
    exact_mod_cast (show 1 ≤ Parameters.legCount security by
      have h : 0 < Parameters.legCount security := Nat.cast_pos.mp hlegsPos; omega)
  have hden : 0 < (Parameters.legCount security : ℝ) * rate :=
    mul_pos hlegsPos (activationApprox_pos security bits)
  have hdenLower : 1 / (8 * (Parameters.base security : ℝ)) ≤
      (Parameters.legCount security : ℝ) * rate :=
    hrateLower.trans (by nlinarith [activationApprox_pos security bits])
  have hdimension : freeMass security + 3 * (Parameters.legCount security : ℝ) +
      Parameters.modulus security = Parameters.dimension security := by
    unfold freeMass Parameters.dimension
    push_cast
    ring
  have hbalance : (Parameters.dimension security : ℝ) / Parameters.modulus security -
      (freeMass security + (Parameters.legCount security : ℝ) * DiffuseProfiles.activation security) * (bodyLaw security false).weight output -
      ((Parameters.legCount security : ℝ) + Parameters.modulus security) * (bodyLaw security true).weight output -
      2 * Parameters.legCount security * (1 - DiffuseProfiles.activation security) * diffuseMean security output =
      (Parameters.legCount security : ℝ) * DiffuseProfiles.activation security * primaryProfile security output := by
    unfold primaryProfile markMass
    field_simp [(DiffuseProfiles.activation_pos security).ne', hlegsPos.ne']
  have hprimary : 0 ≤ primaryProfile security output ∧ primaryProfile security output ≤ 1 :=
    ⟨(primaryLaw security).nonneg output, (primaryLaw security).atom_le_one output⟩
  have hdiffuse : 0 ≤ diffuseMean security output ∧ diffuseMean security output ≤ 1 := by
    refine ⟨diffuseMean_nonneg security output, ?_⟩
    rw [← diffuseMean_mass security]
    exact Finset.single_le_sum (fun color _ => diffuseMean_nonneg security color) (Finset.mem_univ output)
  have hzeroError : |(bodyLaw security false).weight output - (approximateBodyLaw security bits false).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← body_cast]
    exact (_p2mH383 security bits false output).trans_eq (by dsimp only [epsilon]; ring)
  have honeError : |(bodyLaw security true).weight output - (approximateBodyLaw security bits true).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← body_cast]
    exact (_p2mH383 security bits true output).trans_eq (by dsimp only [epsilon]; ring)
  have hdiffuseError : |diffuseMean security output - (approximateDiffuseLaw security bits).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← diffuse_cast]
    exact (_p2mH388 security bits output).trans_eq (by dsimp only [epsilon]; ring)
  have hresidual := _p2mH559 (freeMass security) (Parameters.legCount security)
    (Parameters.modulus security) (Parameters.dimension security) rate (DiffuseProfiles.activation security)
    ((bodyLaw security false).weight output) ((bodyLaw security true).weight output)
    (diffuseMean security output) (primaryProfile security output)
    ((approximateBodyLaw security bits false).weight output) ((approximateBodyLaw security bits true).weight output)
    ((approximateDiffuseLaw security bits).weight output) epsilon (freeMass_nonneg security) hlegsPos.le
    (Nat.cast_nonneg _) hdimension ⟨hrate.1, by linarith only [hrate.2]⟩ hepsilon
    ⟨(bodyLaw security false).nonneg output, (bodyLaw security false).atom_le_one output⟩ hdiffuse hprimary
    hzeroError honeError hdiffuseError hrateError hbalance
  rw [primaryRaw_cast]
  have hquotient (numerator : ℝ) : |numerator / ((Parameters.legCount security : ℝ) * rate) -
      primaryProfile security output| =
      |numerator - (Parameters.legCount security : ℝ) * rate * primaryProfile security output| /
        ((Parameters.legCount security : ℝ) * rate) := by
    rw [div_sub' hden.ne', abs_div, abs_of_pos hden]
  rw [hquotient]
  calc
    _ ≤ (8 * Parameters.dimension security * epsilon) / ((Parameters.legCount security : ℝ) * rate) :=
      div_le_div_of_nonneg_right hresidual hden.le
    _ ≤ (8 * Parameters.dimension security * epsilon) / (1 / (8 * (Parameters.base security : ℝ))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdenLower
    _ = _ := by dsimp only [epsilon]; field_simp; ring
open _root_.P2M9e1cfc64 renaming h390 → _p2mH390
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h391 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : FirstHistogram.Palette security) :
    1 / (4 * (Parameters.modulus security : ℝ)) ≤ (primaryRaw security bits output.val : ℝ) := by
  have herr := (abs_le.mp (_p2mH390 security bits output hprecision)).1
  have hp := primaryProfile_atom_lower security output
  have hfrac : (1 : ℝ) / (2 * Parameters.modulus security) = 2 * (1 / (4 * Parameters.modulus security)) := by ring
  rw [hfrac] at hp
  linarith
open _root_.P2M9e1cfc64 renaming h391 → _p2mH391
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h389 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) : primaryGood security bits := by
  unfold primaryGood
  rw [PublicParameterProgram.modulus_value]
  intro output
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
    _p2mH391 security bits hprecision hbudget output
open _root_.P2M9e1cfc64 renaming h389 → _p2mH389
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h392 (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(primary security bits output.val : ℝ) - primaryProfile security output| ≤
      64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) := by
  rw [primary, if_pos (_p2mH389 security bits hprecision hbudget)]
  exact _p2mH390 security bits output hprecision
open _root_.P2M9e1cfc64 renaming h392 → _p2mH392
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h386 (security bits : ℕ) : (compensationApprox security bits : ℝ) ≤ 1 := by
  apply (compensationApprox_le_leg_body security bits).trans
  apply (div_le_one (bodySize_pos security)).mpr
  exact_mod_cast (show Parameters.legCount security ≤ Parameters.bodySize security by
    have := population_room security; omega)
open _root_.P2M9e1cfc64 renaming h386 → _p2mH386
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h385 (security bits : ℕ) :
    |(compensationApprox security bits : ℝ) - compensation security| ≤ (1 / (2 : ℝ)^bits) / 2 := by
  have hfree := freeMass_pos security
  have hLfree : (Parameters.legCount security : ℝ) ≤ freeMass security := by
    have hp := Nat.cast_le (α := ℝ).mpr (population_room security)
    push_cast at hp
    unfold freeMass
    linarith
  have hratio : (Parameters.legCount security : ℝ) / freeMass security ≤ 1 := (div_le_one hfree).mpr hLfree
  rw [compensationApprox_cast]
  unfold compensation markMass
  have hrewrite : (Parameters.legCount security : ℝ) * LocalPairProgram.activationApprox security bits / freeMass security -
      (Parameters.legCount security : ℝ) * DiffuseProfiles.activation security / freeMass security =
      ((Parameters.legCount security : ℝ) / freeMass security) *
        ((LocalPairProgram.activationApprox security bits : ℝ) - DiffuseProfiles.activation security) := by ring
  rw [hrewrite, abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hfree.le)]
  calc
    _ ≤ ((Parameters.legCount security : ℝ) / freeMass security) *
        ((1 / 2 : ℝ) * (1 / (2 : ℝ)^bits)) :=
      mul_le_mul_of_nonneg_left (_p2mH130 security bits)
        (div_nonneg (Nat.cast_nonneg _) hfree.le)
    _ ≤ 1 * ((1 / 2 : ℝ) * (1 / (2 : ℝ)^bits)) := mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by ring
open _root_.P2M9e1cfc64 renaming h385 → _p2mH385
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h380 (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(anchorPrimary security bits output.val : ℝ) - (anchorPrimaryLaw security).weight output| ≤
      (Parameters.modulus security : ℝ) *
        (64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits)) +
          1 / (2 : ℝ)^bits := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let error : ℝ := 64 * (Parameters.base security : ℝ) * Parameters.dimension security * epsilon
  have hpoint (color : FirstHistogram.Palette security) :
      |(approximatePrimaryLaw security bits).weight color * (approximateAnchorLaw security bits color).weight output -
        (primaryLaw security).weight color * (InwardAnchor.smoothedAnchorLaw security color).weight output| ≤
          error + (primaryLaw security).weight color * epsilon := by
    have hp : |(approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color| ≤ error :=
      _p2mH392 security bits color hprecision hbudget
    have hk : |(approximateAnchorLaw security bits color).weight output -
        (InwardAnchor.smoothedAnchorLaw security color).weight output| ≤ epsilon := by
      rw [← anchor_cast]
      exact _p2mH381 security bits color output
    calc
      _ = |((approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color) *
          (approximateAnchorLaw security bits color).weight output +
          (primaryLaw security).weight color * ((approximateAnchorLaw security bits color).weight output -
            (InwardAnchor.smoothedAnchorLaw security color).weight output)| := by congr 1; ring
      _ ≤ |(approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color| *
          (approximateAnchorLaw security bits color).weight output +
          (primaryLaw security).weight color * |(approximateAnchorLaw security bits color).weight output -
            (InwardAnchor.smoothedAnchorLaw security color).weight output| := by
        simpa only [abs_mul, abs_of_nonneg (FiniteDist.nonneg _ _)] using abs_add_le
          (((approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color) *
            (approximateAnchorLaw security bits color).weight output)
          ((primaryLaw security).weight color * ((approximateAnchorLaw security bits color).weight output -
            (InwardAnchor.smoothedAnchorLaw security color).weight output))
      _ ≤ error * 1 + (primaryLaw security).weight color * epsilon :=
        add_le_add (mul_le_mul hp ((approximateAnchorLaw security bits color).atom_le_one output)
          (FiniteDist.nonneg _ _) (by dsimp only [error, epsilon]; positivity))
          (mul_le_mul_of_nonneg_left hk ((primaryLaw security).nonneg color))
      _ = _ := by ring
  rw [anchorPrimary_cast]
  change |(∑ color, (approximatePrimaryLaw security bits).weight color *
    (approximateAnchorLaw security bits color).weight output) -
    ∑ color, (primaryLaw security).weight color * (InwardAnchor.smoothedAnchorLaw security color).weight output| ≤ _
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ color, (error + (primaryLaw security).weight color * epsilon) :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
      rfl
open _root_.P2M9e1cfc64 renaming h380 → _p2mH380
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h384 (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(center security bits output.val : ℝ) - centerProfile security output| ≤
      (64 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security + 2) *
        (1 / (2 : ℝ)^bits) := by
  have hcomp := _p2mH385 security bits
  have hanchor := _p2mH380 security bits output hprecision hbudget
  rw [anchorPrimary_cast] at hanchor
  have hgap : |(safeLaw security).weight output - (anchorPrimaryLaw security).weight output| ≤ 2 := by
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg ((safeLaw security).nonneg output),
        abs_of_nonneg ((anchorPrimaryLaw security).nonneg output)]
      linarith [(safeLaw security).atom_le_one output, (anchorPrimaryLaw security).atom_le_one output])
  rw [center_cast]
  have hdecompose : approximateCenterProfile security bits output - centerProfile security output =
      ((compensationApprox security bits : ℝ) - compensation security) *
        ((safeLaw security).weight output - (anchorPrimaryLaw security).weight output) -
      (compensationApprox security bits : ℝ) *
        ((approximateAnchorPrimaryLaw security bits).weight output - (anchorPrimaryLaw security).weight output) := by
    unfold approximateCenterProfile centerProfile
    ring
  rw [hdecompose]
  calc
    _ ≤ |(compensationApprox security bits : ℝ) - compensation security| *
        |(safeLaw security).weight output - (anchorPrimaryLaw security).weight output| +
      (compensationApprox security bits : ℝ) *
        |(approximateAnchorPrimaryLaw security bits).weight output - (anchorPrimaryLaw security).weight output| := by
      simpa only [abs_mul, abs_of_nonneg (compensationApprox_nonneg security bits)] using abs_sub
        (((compensationApprox security bits : ℝ) - compensation security) *
          ((safeLaw security).weight output - (anchorPrimaryLaw security).weight output))
        ((compensationApprox security bits : ℝ) *
          ((approximateAnchorPrimaryLaw security bits).weight output - (anchorPrimaryLaw security).weight output))
    _ ≤ ((1 / (2 : ℝ)^bits) / 2) * 2 + 1 *
        ((Parameters.modulus security : ℝ) *
          (64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits)) +
          1 / (2 : ℝ)^bits) :=
      add_le_add (mul_le_mul hcomp hgap (abs_nonneg _) (by positivity))
        (mul_le_mul (_p2mH386 security bits) hanchor (abs_nonneg _) (by positivity))
    _ = _ := by ring
open _root_.P2M9e1cfc64 renaming h384 → _p2mH384
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h382 (security bits : ℕ) (output : ActualControls.SafePalette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(approximateBodyReference security bits).weight output - (ActualControls.bodyReference security).weight output| ≤
      (64 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security + 2) *
        (1 / (2 : ℝ)^bits) :=
  _p2mH384 security bits output.val hprecision hbudget
open _root_.P2M9e1cfc64 renaming h382 → _p2mH382
end
open _root_.P2M9e1cfc64 renaming h380 → _p2mH380
open _root_.P2M9e1cfc64 renaming h381 → _p2mH381
open _root_.P2M9e1cfc64 renaming h382 → _p2mH382
open _root_.P2M9e1cfc64 renaming h383 → _p2mH383
open _root_.P2M9e1cfc64 renaming h384 → _p2mH384
open _root_.P2M9e1cfc64 renaming h385 → _p2mH385
open _root_.P2M9e1cfc64 renaming h386 → _p2mH386
open _root_.P2M9e1cfc64 renaming h387 → _p2mH387
open _root_.P2M9e1cfc64 renaming h388 → _p2mH388
open _root_.P2M9e1cfc64 renaming h389 → _p2mH389
open _root_.P2M9e1cfc64 renaming h390 → _p2mH390
open _root_.P2M9e1cfc64 renaming h391 → _p2mH391
open _root_.P2M9e1cfc64 renaming h392 → _p2mH392
open _root_.P2M9e1cfc64 renaming h393 → _p2mH393
open _root_.P2M9e1cfc64 renaming h559 → _p2mH559
end CurrentAFT.RationalProposalProgram
open _root_.P2M9e1cfc64 renaming h380 → _p2mH380
open _root_.P2M9e1cfc64 renaming h381 → _p2mH381
open _root_.P2M9e1cfc64 renaming h382 → _p2mH382
open _root_.P2M9e1cfc64 renaming h383 → _p2mH383
open _root_.P2M9e1cfc64 renaming h384 → _p2mH384
open _root_.P2M9e1cfc64 renaming h385 → _p2mH385
open _root_.P2M9e1cfc64 renaming h386 → _p2mH386
open _root_.P2M9e1cfc64 renaming h387 → _p2mH387
open _root_.P2M9e1cfc64 renaming h388 → _p2mH388
open _root_.P2M9e1cfc64 renaming h389 → _p2mH389
open _root_.P2M9e1cfc64 renaming h390 → _p2mH390
open _root_.P2M9e1cfc64 renaming h391 → _p2mH391
open _root_.P2M9e1cfc64 renaming h392 → _p2mH392
open _root_.P2M9e1cfc64 renaming h393 → _p2mH393
open _root_.P2M9e1cfc64 renaming h559 → _p2mH559
end
open _root_.P2M9e1cfc64 renaming h383 → _p2mH383
open _root_.P2M9e1cfc64 renaming h386 → _p2mH386
open _root_.P2M9e1cfc64 renaming h388 → _p2mH388
open _root_.P2M9e1cfc64 renaming h390 → _p2mH390
open _root_.P2M9e1cfc64 renaming h392 → _p2mH392
open _root_.P2M9e1cfc64 renaming h393 → _p2mH393
open _root_.P2M9e1cfc64 renaming h385 → _p2mH385
open _root_.P2M9e1cfc64 renaming h381 → _p2mH381
open _root_.P2M9e1cfc64 renaming h387 → _p2mH387
open _root_.P2M9e1cfc64 renaming h391 → _p2mH391
open _root_.P2M9e1cfc64 renaming h382 → _p2mH382
open _root_.P2M9e1cfc64 renaming h389 → _p2mH389
open _root_.P2M9e1cfc64 renaming h384 → _p2mH384
open _root_.P2M9e1cfc64 renaming h380 → _p2mH380
section
namespace CurrentAFT.CurrentCycleEntryProgram
open AFT GaussianSource CycleSelections CyclePatternProgram DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize
attribute [local instance] _root_.CurrentAFT.CurrentCycleEntryProgram.modulusNeZero
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h53 (security : ℕ) : bodyCount security = Parameters.bodySize security := by
  simp only [bodyCount, PublicParameterProgram.modulus_value, Parameters.bodySize_eq, Parameters.base]
open _root_.P2M9e1cfc64 renaming h53 → _p2mH53
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h54 (colors order : ℕ) (output : Fin order → ℕ) (roots : Fin order → ℤ) :
    |(pointTest colors order output roots : ℝ)| ≤ 1 := by
  unfold pointTest
  split_ifs <;> norm_num
open _root_.P2M9e1cfc64 renaming h54 → _p2mH54
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h55 (security order : ℕ) (roots : Fin order → ℤ)
    (output : Fin order → CycleRootExpansion.Root security) :
    (∀ index, roots index % Parameters.modulus security = ((output index).val : ℤ)) ↔
      (fun index => (roots index : CycleRootExpansion.Root security)) = output := by
  have hpoint (integer : ℤ) (color : CycleRootExpansion.Root security) :
      integer % Parameters.modulus security = (color.val : ℤ) ↔
        (integer : CycleRootExpansion.Root security) = color := by
    rw [← ZMod.val_intCast]
    constructor
    · intro hequal
      apply ZMod.val_injective
      exact Int.ofNat_inj.mp hequal
    · intro hequal
      rw [hequal]
  constructor
  · intro h
    funext index
    exact (hpoint _ _).mp (h index)
  · intro h index
    exact (hpoint _ _).mpr (congrFun h index)
open _root_.P2M9e1cfc64 renaming h55 → _p2mH55
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h59 (security order : ℕ)
    (source : FiniteDist (Window (edgeCutoff security)))
    (sites : Selection (Parameters.bodySize security) order)
    (output : Fin order → CycleRootExpansion.Root security) :
    (FiniteDist.independent (fun _ : CycleRootExpansion.Vertex security => source)).expectation
      (fun latent => (pointTest (Parameters.modulus security) order (fun index => (output index).val)
        (fun slot => (latent (sites slot)).val -
          (latent ((finRotate (Parameters.bodySize security)).symm (sites slot))).val) : ℝ)) =
      (selectedLaw (Parameters.bodySize security) order (Parameters.modulus security)
        (source) (fun scalar => ((scalar.val : ℤ) : CycleRootExpansion.Root security)) sites).weight output := by
  rw [selectedLaw, ProtectedCycle.cycleLaw, FiniteDist.map_map]
  simp only [FiniteDist.expectation, FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro latent _
  have hequal : (fun slot => PublicCharge.cycleDifference
      (fun vertex => ((latent vertex).val : CycleRootExpansion.Root security)) (sites slot)) = output ↔
      ∀ slot, ((latent (sites slot)).val -
        (latent ((finRotate (Parameters.bodySize security)).symm (sites slot))).val) %
          Parameters.modulus security = ((output slot).val : ℤ) := by
    rw [_p2mH55]
    simp only [PublicCharge.cycleDifference, Int.cast_sub]
  unfold pointTest
  by_cases hactual : (fun slot => PublicCharge.cycleDifference
      (fun vertex => ((latent vertex).val : CycleRootExpansion.Root security)) (sites slot)) = output
  · simp only [if_pos hactual, if_pos (hequal.mp hactual), Rat.cast_one, mul_one]
  · have hmod := mt hequal.mpr hactual
    simp only [if_neg hactual, if_neg hmod, Rat.cast_zero, mul_zero]
open _root_.P2M9e1cfc64 renaming h59 → _p2mH59
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h58 (security order : ℕ)
    (sites : Selection (Parameters.bodySize security) order)
    (output : Fin order → CycleRootExpansion.Root security) :
    (FiniteDist.independent (fun _ : CycleRootExpansion.Vertex security => edgeLaw security)).expectation
      (fun latent => (pointTest (Parameters.modulus security) order (fun index => (output index).val)
        (fun slot => (latent (sites slot)).val -
          (latent ((finRotate (Parameters.bodySize security)).symm (sites slot))).val) : ℝ)) =
      (selectedLaw (Parameters.bodySize security) order (Parameters.modulus security)
        (edgeLaw security) (fun scalar => ((scalar.val : ℤ) : CycleRootExpansion.Root security)) sites).weight output :=
  _p2mH59 security order (edgeLaw security) sites output
open _root_.P2M9e1cfc64 renaming h58 → _p2mH58
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h57 (security bits order : ℕ) (hroom : order ≤ Parameters.bodySize security)
    (output : Fin order → CycleRootExpansion.Root security) :
    |(selectedEntry security bits order (fun index => (output index).val) : ℝ) -
      (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) hroom
        (edgeLaw security) (fun scalar => ((scalar.val : ℤ) : CycleRootExpansion.Root security))).weight output| ≤
      (2 * order : ℕ) / (2 : ℝ)^bits := by
  unfold selectedEntry
  rw [_p2mH53, PublicParameterProgram.modulus_value]
  have h := _p2mH66 security bits (Parameters.bodySize security) order hroom
    (fun _ => pointTest (Parameters.modulus security) order (fun index => (output index).val))
    1 (by norm_num) (fun _ roots => _p2mH54 _ _ _ roots)
  simp only [mul_one] at h
  have hideal : (selectionLaw (Parameters.bodySize security) order hroom).expectation
      (fun sites => (FiniteDist.independent (fun _ : CycleRootExpansion.Vertex security => edgeLaw security)).expectation
        (fun latent => (pointTest (Parameters.modulus security) order (fun index => (output index).val)
          (fun slot => (latent (sites slot)).val -
            (latent ((finRotate (Parameters.bodySize security)).symm (sites slot))).val) : ℝ))) =
      (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) hroom
        (edgeLaw security) (fun scalar => ((scalar.val : ℤ) : CycleRootExpansion.Root security))).weight output := by
    simp_rw [_p2mH58]
    rfl
  rw [hideal] at h
  exact h
open _root_.P2M9e1cfc64 renaming h57 → _p2mH57
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h56 (security bits order : ℕ) (hroom : order ≤ Parameters.bodySize security)
    (output : Fin order → CycleRootExpansion.Root security) :
    (selectedEntry security bits order (fun index => (output index).val) : ℝ) =
      (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) hroom
        (RationalNumerics.windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits)
        (fun scalar => ((scalar.val : ℤ) : CycleRootExpansion.Root security))).weight output := by
  unfold selectedEntry
  rw [_p2mH53, PublicParameterProgram.modulus_value,
    _p2mH65 security (edgeCutoff security) bits (Parameters.bodySize security) order hroom]
  simp_rw [_p2mH73, _p2mH59]
  rfl
open _root_.P2M9e1cfc64 renaming h56 → _p2mH56
end
open _root_.P2M9e1cfc64 renaming h53 → _p2mH53
open _root_.P2M9e1cfc64 renaming h54 → _p2mH54
open _root_.P2M9e1cfc64 renaming h55 → _p2mH55
open _root_.P2M9e1cfc64 renaming h56 → _p2mH56
open _root_.P2M9e1cfc64 renaming h57 → _p2mH57
open _root_.P2M9e1cfc64 renaming h58 → _p2mH58
open _root_.P2M9e1cfc64 renaming h59 → _p2mH59
end CurrentAFT.CurrentCycleEntryProgram
open _root_.P2M9e1cfc64 renaming h53 → _p2mH53
open _root_.P2M9e1cfc64 renaming h54 → _p2mH54
open _root_.P2M9e1cfc64 renaming h55 → _p2mH55
open _root_.P2M9e1cfc64 renaming h56 → _p2mH56
open _root_.P2M9e1cfc64 renaming h57 → _p2mH57
open _root_.P2M9e1cfc64 renaming h58 → _p2mH58
open _root_.P2M9e1cfc64 renaming h59 → _p2mH59
end
open _root_.P2M9e1cfc64 renaming h57 → _p2mH57
open _root_.P2M9e1cfc64 renaming h54 → _p2mH54
open _root_.P2M9e1cfc64 renaming h59 → _p2mH59
open _root_.P2M9e1cfc64 renaming h56 → _p2mH56
open _root_.P2M9e1cfc64 renaming h55 → _p2mH55
open _root_.P2M9e1cfc64 renaming h53 → _p2mH53
open _root_.P2M9e1cfc64 renaming h58 → _p2mH58
section
namespace CurrentAFT.GroupSourcePadding
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h86 (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) (kind : Kind)
    (word : Fin 3 → Fin q) (h : Valid q safe kind word) :
    encode q hq safe kind (recover q safe kind word h) = word := by
  funext slot
  cases kind with
  | primary => fin_cases slot <;> rfl
  | ordinary =>
    fin_cases slot
    · rfl
    · rfl
    · apply Fin.ext; exact h.2.symm
  | kept =>
    fin_cases slot
    · rfl
    · apply Fin.ext; exact h.1.symm
    · apply Fin.ext; exact h.2.symm
open _root_.P2M9e1cfc64 renaming h86 → _p2mH86
section Grouped
variable {Group : Type*} [Fintype Group] (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) [DecidablePred safe]
  (kind : Group → Kind)
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h88 (source : Source q safe kind) :
    sourceDecode q safe kind (sourceEncode q hq safe kind source) = some source := by
  unfold sourceDecode sourceEncode
  rw [dif_pos (fun group => encode_valid q hq safe (kind group) (source group))]
  congr 1
  funext group
  exact recover_encode q hq safe (kind group) (source group)
open _root_.P2M9e1cfc64 renaming h88 → _p2mH88
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h89 (word : Word (Group := Group) q) (source : Source q safe kind) :
    sourceDecode q safe kind word = some source ↔ word = sourceEncode q hq safe kind source := by
  constructor
  · intro h
    unfold sourceDecode at h
    split at h
    · rename_i hv
      have he := Option.some.inj h
      subst source
      funext group
      exact (_p2mH86 q hq safe (kind group) (word group) (hv group)).symm
    · cases h
  · rintro rfl
    exact _p2mH88 q hq safe kind source
open _root_.P2M9e1cfc64 renaming h89 → _p2mH89
end Grouped
open _root_.P2M9e1cfc64 renaming h88 → _p2mH88
open _root_.P2M9e1cfc64 renaming h89 → _p2mH89
section Indexed
variable {Group : Type*} [Fintype Group] [DecidableEq Group] (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) [DecidablePred safe]
  (kind : Group → Kind) (count : ℕ) (ordering : Fin count ≃ Group)
set_option maxRecDepth 8192
omit [DecidableEq Group] in
theorem _root_.P2M9e1cfc64.h87 (index : Fin (q^(count*3))) (source : Source q safe kind) :
    indexDecode q hq safe kind count ordering index = some source ↔
      index = indexEncode q hq safe kind count ordering source := by
  rw [indexDecode, _p2mH89 q hq safe kind]
  exact (indexEquiv q hq count ordering).symm_apply_eq
open _root_.P2M9e1cfc64 renaming h87 → _p2mH87
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h90 {Scalar : Type*} [AddCommMonoid Scalar] (summand : Source q safe kind → Scalar) :
    (∑ index : Fin (q^(count*3)), (indexDecode q hq safe kind count ordering index).elim 0 summand) =
      ∑ source, summand source :=
  _p2mH50 (indexEncode q hq safe kind count ordering)
    (indexDecode q hq safe kind count ordering) (_p2mH87 q hq safe kind count ordering) summand
open _root_.P2M9e1cfc64 renaming h90 → _p2mH90
end Indexed
open _root_.P2M9e1cfc64 renaming h87 → _p2mH87
open _root_.P2M9e1cfc64 renaming h90 → _p2mH90
end CurrentAFT.GroupSourcePadding
open _root_.P2M9e1cfc64 renaming h86 → _p2mH86
open _root_.P2M9e1cfc64 renaming h87 → _p2mH87
open _root_.P2M9e1cfc64 renaming h88 → _p2mH88
open _root_.P2M9e1cfc64 renaming h89 → _p2mH89
open _root_.P2M9e1cfc64 renaming h90 → _p2mH90
end
open _root_.P2M9e1cfc64 renaming h90 → _p2mH90
open _root_.P2M9e1cfc64 renaming h88 → _p2mH88
open _root_.P2M9e1cfc64 renaming h89 → _p2mH89
open _root_.P2M9e1cfc64 renaming h87 → _p2mH87
open _root_.P2M9e1cfc64 renaming h86 → _p2mH86
section
namespace CurrentAFT.RootSignedMassProgram
open AFT GaussianSource CycleSelections CyclePatternProgram CycleRootExpansion
  CurrentCycleEntryProgram DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize
attribute [local instance] _root_.CurrentAFT.RootSignedMassProgram.modulusNeZero
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h530 (Index Color : Type*) [Fintype Index] [DecidableEq Index] [Fintype Color] [DecidableEq Color]
    (joint : FiniteDist (Index → Color)) (reference : Index → FiniteDist Color)
    (hsupport : ∀ input, joint.weight input ≠ 0 → ∀ index, 0 < (reference index).weight (input index))
    (output : Index → Color) :
    (∏ index, (reference index).weight (output index)) * centeredRootDensity joint reference output =
      joint.expectation (fun input => ∏ index,
        ((if input index = output index then (1 : ℝ) else 0) - (reference index).weight (output index))) := by
  unfold centeredRootDensity FiniteDist.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  by_cases hzero : joint.weight input = 0
  · simp only [hzero, zero_mul, mul_zero]
  · have hpoint (index : Index) : (reference index).weight (output index) *
        centeredRootAtom (reference index) (input index) (output index) =
          (if input index = output index then (1 : ℝ) else 0) - (reference index).weight (output index) := by
      by_cases hout : (reference index).weight (output index) = 0
      · have hne : input index ≠ output index := by
          intro hequal
          have hpos := hsupport input hzero index
          rw [hequal, hout] at hpos
          exact (lt_irrefl 0) hpos
        simp only [centeredRootAtom, hout, hne, if_false, zero_mul, sub_zero]
      · unfold centeredRootAtom
        by_cases hequal : input index = output index
        · simp only [if_pos hequal]
          field_simp
        · simp only [if_neg hequal]
          field_simp
    calc
      _ = joint.weight input *
          ((∏ index, (reference index).weight (output index)) *
            ∏ index, centeredRootAtom (reference index) (input index) (output index)) := by ring
      _ = joint.weight input * (∏ index, (reference index).weight (output index) *
          centeredRootAtom (reference index) (input index) (output index)) := by rw [Finset.prod_mul_distrib]
      _ = _ := by congr 1; exact Finset.prod_congr rfl (fun index _ => hpoint index)
open _root_.P2M9e1cfc64 renaming h530 → _p2mH530
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h519 (security order : ℕ)
    (labels : Selection (Parameters.bodySize security) order) (output : Fin order → Root security) :
    (∏ index, (rootReference security).weight (output index)) * selectedCoefficient security order labels output =
      ((rootLaw security).map (fun roots index => roots (labels index))).expectation
        (fun input => ∏ index, ((if input index = output index then (1 : ℝ) else 0) -
          (rootReference security).weight (output index))) := by
  unfold selectedCoefficient
  apply _p2mH530
  apply _p2mH77
  intro index
  rw [FiniteDist.map_map]
  exact _p2mH78 security (labels index)
open _root_.P2M9e1cfc64 renaming h519 → _p2mH519
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h527 (security : ℕ) (source : FiniteDist (Window (edgeCutoff security)))
    (output : Root security) :
    (averagedSelectedLaw (Parameters.bodySize security) 1 (Parameters.modulus security)
      (by have := _p2mH76 security; omega) source
      (fun scalar => ((scalar.val : ℤ) : Root security))).weight (fun _ => output) =
        (ProtectedCycle.differenceLaw source (fun scalar => ((scalar.val : ℤ) : Root security))).weight output := by
  have h := congrArg (fun law : FiniteDist (Root security) => law.weight output)
    (_p2mH79 (Parameters.bodySize security) 1 (Parameters.modulus security)
      (by have := _p2mH76 security; omega) (_p2mH76 security) source
      (fun scalar => ((scalar.val : ℤ) : Root security)) 0)
  change ((averagedSelectedLaw (Parameters.bodySize security) 1 (Parameters.modulus security) _ source _).map
    (oneEquiv (Root security))).weight output = _ at h
  rw [FiniteDist.map_equiv_weight] at h
  exact h
open _root_.P2M9e1cfc64 renaming h527 → _p2mH527
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h521 (security bits : ℕ) (output : Root security) :
    (referenceEntry security bits output.val : ℝ) =
      (ProtectedCycle.differenceLaw
        (RationalNumerics.windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits)
        (fun scalar => ((scalar.val : ℤ) : Root security))).weight output := by
  rw [referenceEntry, _p2mH56 security bits 1 (by have := _p2mH76 security; omega)
    (fun _ => output), _p2mH527]
open _root_.P2M9e1cfc64 renaming h521 → _p2mH521
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h520 (security bits : ℕ) (output : Root security) :
    0 ≤ (referenceEntry security bits output.val : ℝ) ∧ (referenceEntry security bits output.val : ℝ) ≤ 1 := by
  rw [_p2mH521]
  exact ⟨FiniteDist.nonneg _ _, FiniteDist.atom_le_one _ _⟩
open _root_.P2M9e1cfc64 renaming h520 → _p2mH520
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h522 (security bits : ℕ) (output : Root security) :
    |(referenceEntry security bits output.val : ℝ) - (rootReference security).weight output| ≤
      2 / (2 : ℝ)^bits := by
  have h := _p2mH57 security bits 1 (by have := _p2mH76 security; omega) (fun _ => output)
  rw [_p2mH527] at h
  exact h
open _root_.P2M9e1cfc64 renaming h522 → _p2mH522
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h523 (security : ℕ) (integer : ℤ) (output : Root security) :
    integer % Parameters.modulus security = (output.val : ℤ) ↔ (integer : Root security) = output := by
  rw [← ZMod.val_intCast]
  constructor
  · intro h
    apply ZMod.val_injective
    exact Int.ofNat_inj.mp h
  · intro h
    rw [h]
open _root_.P2M9e1cfc64 renaming h523 → _p2mH523
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h526 (security bits order : ℕ) (output : Fin order → Root security) (roots : Fin order → ℤ) :
    (signedTest security bits order (fun index => (output index).val) roots : ℝ) =
      ∏ index, ((if (roots index : Root security) = output index then (1 : ℝ) else 0) -
        (referenceEntry security bits (output index).val : ℝ)) := by
  simp only [signedTest, PublicParameterProgram.modulus_value, Rat.cast_prod, Rat.cast_sub]
  apply Finset.prod_congr rfl
  intro index _
  by_cases hequal : (roots index : Root security) = output index
  · rw [if_pos ((_p2mH523 security _ _).mpr hequal), if_pos hequal, Rat.cast_one]
  · rw [if_neg (mt (_p2mH523 security _ _).mp hequal), if_neg hequal, Rat.cast_zero]
open _root_.P2M9e1cfc64 renaming h526 → _p2mH526
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h525 (security bits order : ℕ) (output : Fin order → Root security) (roots : Fin order → ℤ) :
    |(signedTest security bits order (fun index => (output index).val) roots : ℝ)| ≤ 1 := by
  rw [_p2mH526, Finset.abs_prod]
  apply Finset.prod_le_one
  · intro _ _
    exact abs_nonneg _
  · intro index _
    have h := _p2mH520 security bits (output index)
    split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2M9e1cfc64 renaming h525 → _p2mH525
set_option maxRecDepth 8192
private theorem _root_.P2M9e1cfc64.h561 {Index : Type*} [DecidableEq Index]
    (first second : Index → ℝ) (hfirst : ∀ index, |first index| ≤ 1) (hsecond : ∀ index, |second index| ≤ 1)
    (indices : Finset Index) :
    |(∏ index ∈ indices, first index) - ∏ index ∈ indices, second index| ≤
      ∑ index ∈ indices, |first index - second index| := by
  have hprod (set : Finset Index) : |∏ index ∈ set, second index| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun index _ => hsecond index)
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hnot ih =>
    rw [Finset.prod_insert hnot, Finset.prod_insert hnot, Finset.sum_insert hnot]
    have hrewrite : first index * (∏ other ∈ indices, first other) -
        second index * (∏ other ∈ indices, second other) =
        first index * ((∏ other ∈ indices, first other) - ∏ other ∈ indices, second other) +
          (first index - second index) * (∏ other ∈ indices, second other) := by ring
    rw [hrewrite]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    calc
      _ ≤ 1 * (∑ other ∈ indices, |first other - second other|) + |first index - second index| * 1 :=
        add_le_add (mul_le_mul (hfirst index) ih (abs_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left (hprod indices) (abs_nonneg _))
      _ = _ := by ring
open _root_.P2M9e1cfc64 renaming h561 → _p2mH561
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h529 (security bits order : ℕ) (hroom : order ≤ Parameters.bodySize security)
    (output : Fin order → Root security) :
    |(weightedEntry security bits order (fun index => (output index).val) : ℝ) -
      (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) hroom
        (edgeLaw security) (fun scalar => ((scalar.val : ℤ) : Root security))).expectation
          (signedKernel security bits order output)| ≤ (2 * order : ℕ) / (2 : ℝ)^bits := by
  unfold weightedEntry
  rw [_p2mH53]
  have h := _p2mH66 security bits (Parameters.bodySize security) order hroom
    (fun _ => signedTest security bits order (fun index => (output index).val)) 1 (by norm_num)
    (fun _ roots => _p2mH525 security bits order output roots)
  simp only [mul_one] at h
  have hideal : (selectionLaw (Parameters.bodySize security) order hroom).expectation
      (fun sites => (FiniteDist.independent (fun _ : Vertex security => edgeLaw security)).expectation
        (fun latent => (signedTest security bits order (fun index => (output index).val)
          (fun slot => (latent (sites slot)).val -
            (latent ((finRotate (Parameters.bodySize security)).symm (sites slot))).val) : ℝ))) =
      (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) hroom
        (edgeLaw security) (fun scalar => ((scalar.val : ℤ) : Root security))).expectation
          (signedKernel security bits order output) := by
    rw [averagedSelectedLaw, FiniteDist.expectation_mix]
    apply congrArg (FiniteDist.expectation _)
    funext sites
    rw [selectedLaw, ProtectedCycle.cycleLaw, FiniteDist.expectation_map, FiniteDist.expectation_map]
    apply congrArg (FiniteDist.expectation _)
    funext latent
    rw [_p2mH526]
    unfold signedKernel
    apply Finset.prod_congr rfl
    intro index _
    simp only [PublicCharge.cycleDifference, Int.cast_sub]
  rw [hideal] at h
  exact h
open _root_.P2M9e1cfc64 renaming h529 → _p2mH529
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h524 (security bits order : ℕ) (output input : Fin order → Root security) :
    |signedKernel security bits order output input -
      (∏ index, ((if input index = output index then (1 : ℝ) else 0) -
        (rootReference security).weight (output index)))| ≤ (2 * order : ℕ) / (2 : ℝ)^bits := by
  have hdelta (index : Fin order) (rate : ℝ) (hrate : 0 ≤ rate ∧ rate ≤ 1) :
      |(if input index = output index then (1 : ℝ) else 0) - rate| ≤ 1 := by
    split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  apply (_p2mH561
    (fun index => (if input index = output index then (1 : ℝ) else 0) -
      (referenceEntry security bits (output index).val : ℝ))
    (fun index => (if input index = output index then (1 : ℝ) else 0) -
      (rootReference security).weight (output index))
    (fun index => hdelta index _ (_p2mH520 security bits (output index)))
    (fun index => hdelta index _ ⟨(rootReference security).nonneg _, (rootReference security).atom_le_one _⟩)
    Finset.univ).trans
  calc
    _ ≤ ∑ _index : Fin order, 2 / (2 : ℝ)^bits := by
      apply Finset.sum_le_sum
      intro index _
      have hequal : ((if input index = output index then (1 : ℝ) else 0) -
          (referenceEntry security bits (output index).val : ℝ)) -
          ((if input index = output index then (1 : ℝ) else 0) -
            (rootReference security).weight (output index)) =
          -((referenceEntry security bits (output index).val : ℝ) -
            (rootReference security).weight (output index)) := by ring
      rw [hequal, abs_neg]
      exact _p2mH522 security bits (output index)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]; ring
open _root_.P2M9e1cfc64 renaming h524 → _p2mH524
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h528 (security bits order : ℕ) (hroom : order ≤ Parameters.bodySize security)
    (labels : Selection (Parameters.bodySize security) order) (output : Fin order → Root security) :
    |(weightedEntry security bits order (fun index => (output index).val) : ℝ) -
      (∏ index, (rootReference security).weight (output index)) * selectedCoefficient security order labels output| ≤
      (4 * order : ℕ) / (2 : ℝ)^bits := by
  let joint := averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) hroom
    (edgeLaw security) (fun scalar => ((scalar.val : ℤ) : Root security))
  have hweighted := _p2mH519 security order labels output
  rw [rootLaw_selected security order hroom labels] at hweighted
  rw [hweighted]
  have hkernel : |joint.expectation (signedKernel security bits order output) -
      joint.expectation (fun input => ∏ index, ((if input index = output index then (1 : ℝ) else 0) -
        (rootReference security).weight (output index)))| ≤ (2 * order : ℕ) / (2 : ℝ)^bits := by
    rw [← FiniteDist.expectation_sub]
    exact _p2mH2 joint _ _ (_p2mH524 security bits order output)
  calc
    _ ≤ |(weightedEntry security bits order (fun index => (output index).val) : ℝ) -
        joint.expectation (signedKernel security bits order output)| +
      |joint.expectation (signedKernel security bits order output) -
        joint.expectation (fun input => ∏ index, ((if input index = output index then (1 : ℝ) else 0) -
          (rootReference security).weight (output index)))| := abs_sub_le _ _ _
    _ ≤ (2 * order : ℕ) / (2 : ℝ)^bits + (2 * order : ℕ) / (2 : ℝ)^bits :=
      add_le_add (_p2mH529 security bits order hroom output) hkernel
    _ = _ := by push_cast; ring
open _root_.P2M9e1cfc64 renaming h528 → _p2mH528
end
open _root_.P2M9e1cfc64 renaming h519 → _p2mH519
open _root_.P2M9e1cfc64 renaming h520 → _p2mH520
open _root_.P2M9e1cfc64 renaming h521 → _p2mH521
open _root_.P2M9e1cfc64 renaming h522 → _p2mH522
open _root_.P2M9e1cfc64 renaming h523 → _p2mH523
open _root_.P2M9e1cfc64 renaming h524 → _p2mH524
open _root_.P2M9e1cfc64 renaming h525 → _p2mH525
open _root_.P2M9e1cfc64 renaming h526 → _p2mH526
open _root_.P2M9e1cfc64 renaming h527 → _p2mH527
open _root_.P2M9e1cfc64 renaming h528 → _p2mH528
open _root_.P2M9e1cfc64 renaming h529 → _p2mH529
open _root_.P2M9e1cfc64 renaming h530 → _p2mH530
open _root_.P2M9e1cfc64 renaming h561 → _p2mH561
end CurrentAFT.RootSignedMassProgram
open _root_.P2M9e1cfc64 renaming h519 → _p2mH519
open _root_.P2M9e1cfc64 renaming h520 → _p2mH520
open _root_.P2M9e1cfc64 renaming h521 → _p2mH521
open _root_.P2M9e1cfc64 renaming h522 → _p2mH522
open _root_.P2M9e1cfc64 renaming h523 → _p2mH523
open _root_.P2M9e1cfc64 renaming h524 → _p2mH524
open _root_.P2M9e1cfc64 renaming h525 → _p2mH525
open _root_.P2M9e1cfc64 renaming h526 → _p2mH526
open _root_.P2M9e1cfc64 renaming h527 → _p2mH527
open _root_.P2M9e1cfc64 renaming h528 → _p2mH528
open _root_.P2M9e1cfc64 renaming h529 → _p2mH529
open _root_.P2M9e1cfc64 renaming h530 → _p2mH530
open _root_.P2M9e1cfc64 renaming h561 → _p2mH561
end
open _root_.P2M9e1cfc64 renaming h522 → _p2mH522
open _root_.P2M9e1cfc64 renaming h530 → _p2mH530
open _root_.P2M9e1cfc64 renaming h525 → _p2mH525
open _root_.P2M9e1cfc64 renaming h527 → _p2mH527
open _root_.P2M9e1cfc64 renaming h521 → _p2mH521
open _root_.P2M9e1cfc64 renaming h526 → _p2mH526
open _root_.P2M9e1cfc64 renaming h529 → _p2mH529
open _root_.P2M9e1cfc64 renaming h523 → _p2mH523
open _root_.P2M9e1cfc64 renaming h520 → _p2mH520
open _root_.P2M9e1cfc64 renaming h519 → _p2mH519
open _root_.P2M9e1cfc64 renaming h528 → _p2mH528
open _root_.P2M9e1cfc64 renaming h524 → _p2mH524
section
namespace CurrentAFT.RootMassColumns
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  LocalReferenceEnergy FirstHistogram ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
attribute [local instance] _root_.CurrentAFT.RootMassColumns.classicalFinDecidableEq
section Fiber
variable {Root Control Output : Type*} [Fintype Root]
  [AddCommMonoid Output] [Module ℝ Output]
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h494 (reference : FiniteDist Root)
    (channel : Root → (Control → ℝ) →ₗ[ℝ] Output)
    (root : Root) (score : Control → ℝ) :
    (∑ other, reference.weight other • channel other (fiber root score other)) =
      reference.weight root • channel root score := by
  classical
  calc
    _ = reference.weight root • channel root (fiber root score root) :=
      Finset.sum_eq_single root (fun other _ hne => by
        simp only [fiber, if_neg hne, map_zero, smul_zero]) (by simp)
    _ = _ := by simp [fiber]
open _root_.P2M9e1cfc64 renaming h494 → _p2mH494
end Fiber
open _root_.P2M9e1cfc64 renaming h494 → _p2mH494
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h489 (security : ℕ)
    (score : RootTaggedSelected.RootPair security → ActualControls.Palette security → ℝ) :
    RootTaggedSelected.massLinear security score =
      ∑ roots, (RootTaggedSelected.rootsLaw security).weight roots •
        primaryMassAt security roots (score roots) := by
  funext word
  simp only [RootTaggedSelected.massLinear, RootTaggedSelected.sourceLaw, primaryMassAt,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FiniteDist.prod_weight, Fintype.sum_prod_type,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro roots _
  apply Finset.sum_congr rfl
  intro scalar _
  simp only [mul_assoc]
open _root_.P2M9e1cfc64 renaming h489 → _p2mH489
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h490 (security : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : ActualControls.Palette security → ℝ) :
    RootTaggedSelected.massLinear security (fiber roots score) =
      (RootTaggedSelected.rootsLaw security).weight roots • primaryMassAt security roots score := by
  rw [_p2mH489]
  exact _p2mH494 _ (primaryMassAt security) roots score
open _root_.P2M9e1cfc64 renaming h490 → _p2mH490
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h491 (security order : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : ActualControls.Palette security → ℝ) :
    RootTaggedSelectedChannel.responseLinear security order (fiber roots score) =
      (RootTaggedSelected.rootsLaw security).weight roots • primaryResponseAt security order roots score := by
  change LocalRaisingLinear.completeFamilyLinear security order
    (RootTaggedSelected.massLinear security (fiber roots score)) * _ = _
  rw [_p2mH490, map_smul, smul_mul_assoc]
  rfl
open _root_.P2M9e1cfc64 renaming h491 → _p2mH491
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h492 (security : ℕ) (roots : RootTaggedSelected.RootPair security) :
    (RootTaggedSelected.rootsLaw security).weight roots =
      (rootReference security).weight roots.1 * (rootReference security).weight roots.2 := rfl
open _root_.P2M9e1cfc64 renaming h492 → _p2mH492
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h488 (security : ℕ) (root : CycleRootExpansion.Root security)
    (score : SafePalette security → ℝ) :
    SelectedOrdinaryRoot.rawMassLinear security (fun sample => fiber root score sample.1 sample.2) =
      (rootReference security).weight root • ordinaryMassAt security root score := by
  change (∑ other, (rootReference security).weight other •
    (SelectedOrdinaryRoot.pushLinear (bodyReference security) (SelectedOrdinaryRoot.rootEmbedding security other)).comp
      (SelectedOrdinaryRoot.sliceLinear security other)) (fun sample => fiber root score sample.1 sample.2) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change (∑ other, (rootReference security).weight other • ordinaryMassAt security other
    (fiber root score other)) = _
  exact _p2mH494 _ (ordinaryMassAt security) root score
open _root_.P2M9e1cfc64 renaming h488 → _p2mH488
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h493 (security : ℕ) (role : UniformBodyProfiles.BodyRole) (queue : ℤ)
    (root : CycleRootExpansion.Root security) :
    RootTaggedLocal.rootMass security role queue (Pi.single root 1) =
      (rootReference security).weight root • RootTaggedLocal.deviationProfile security role queue root := by
  funext color
  simp [RootTaggedLocal.rootMass, Pi.single_apply]
open _root_.P2M9e1cfc64 renaming h493 → _p2mH493
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h487 (security : ℕ) (root : CycleRootExpansion.Root security) :
    RootTaggedLegHigher.rawMassLinear security (Pi.single root 1) =
      (rootReference security).weight root • (ActualBlockFock.primaryLawAt security root.val).weight := by
  funext word
  simp [RootTaggedLegHigher.rawMassLinear, Pi.single_apply]
open _root_.P2M9e1cfc64 renaming h487 → _p2mH487
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h486 (security : ℕ) (root : CycleRootExpansion.Root security) :
    RootTaggedLegHigher.massLinear security (Pi.single root 1) =
      (rootReference security).weight root •
        ((ActualBlockFock.primaryLawAt security root.val).weight -
          RootTaggedLegHigher.rawMassLinear security (fun _ => 1)) := by
  have hcenter : TensorChannel.center (rootReference security) (Pi.single root 1) =
      Pi.single root 1 - (rootReference security).weight root • (fun _ => (1 : ℝ)) := by
    funext other
    simp only [TensorChannel.center_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    congr 1
    simp [FiniteDist.expectation, Pi.single_apply]
  rw [RootTaggedLegHigher.massLinear, LinearMap.comp_apply, hcenter, map_sub, map_smul,
    _p2mH487, smul_sub]
open _root_.P2M9e1cfc64 renaming h486 → _p2mH486
end
open _root_.P2M9e1cfc64 renaming h486 → _p2mH486
open _root_.P2M9e1cfc64 renaming h487 → _p2mH487
open _root_.P2M9e1cfc64 renaming h488 → _p2mH488
open _root_.P2M9e1cfc64 renaming h489 → _p2mH489
open _root_.P2M9e1cfc64 renaming h490 → _p2mH490
open _root_.P2M9e1cfc64 renaming h491 → _p2mH491
open _root_.P2M9e1cfc64 renaming h492 → _p2mH492
open _root_.P2M9e1cfc64 renaming h493 → _p2mH493
open _root_.P2M9e1cfc64 renaming h494 → _p2mH494
end CurrentAFT.RootMassColumns
open _root_.P2M9e1cfc64 renaming h486 → _p2mH486
open _root_.P2M9e1cfc64 renaming h487 → _p2mH487
open _root_.P2M9e1cfc64 renaming h488 → _p2mH488
open _root_.P2M9e1cfc64 renaming h489 → _p2mH489
open _root_.P2M9e1cfc64 renaming h490 → _p2mH490
open _root_.P2M9e1cfc64 renaming h491 → _p2mH491
open _root_.P2M9e1cfc64 renaming h492 → _p2mH492
open _root_.P2M9e1cfc64 renaming h493 → _p2mH493
open _root_.P2M9e1cfc64 renaming h494 → _p2mH494
end
open _root_.P2M9e1cfc64 renaming h492 → _p2mH492
open _root_.P2M9e1cfc64 renaming h494 → _p2mH494
open _root_.P2M9e1cfc64 renaming h488 → _p2mH488
open _root_.P2M9e1cfc64 renaming h486 → _p2mH486
open _root_.P2M9e1cfc64 renaming h489 → _p2mH489
open _root_.P2M9e1cfc64 renaming h490 → _p2mH490
open _root_.P2M9e1cfc64 renaming h487 → _p2mH487
open _root_.P2M9e1cfc64 renaming h493 → _p2mH493
open _root_.P2M9e1cfc64 renaming h491 → _p2mH491
section
namespace CurrentAFT.RootReferenceColumns
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates GradedControlAlgebra CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootReferenceColumns.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootReferenceColumns.safeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h512 (security : ℕ) (source : RootPrimaryGroupedChannel.Input security) :
    RootTaggedSelectedChannel.curryLinear security
      (RootPrimaryGroupedChannel.pairLinear security (Pi.single source 1)) =
        RootMassColumns.fiber (RootPrimaryGroupedChannel.pairEquiv security source.1) (Pi.single source.2 1) := by
  funext roots primaryColor
  change (Pi.single (M := fun _ : RootPrimaryGroupedChannel.Input security => ℝ) source (1 : ℝ))
    ((RootPrimaryGroupedChannel.pairEquiv security).symm roots, primaryColor) = _
  have hroot : (RootPrimaryGroupedChannel.pairEquiv security).symm roots = source.1 ↔
      roots = RootPrimaryGroupedChannel.pairEquiv security source.1 := by
    constructor
    · intro h
      simpa using congrArg (RootPrimaryGroupedChannel.pairEquiv security) h
    · intro h
      rw [h, Equiv.symm_apply_apply]
  by_cases hr : roots = RootPrimaryGroupedChannel.pairEquiv security source.1
  · have hpair : ((RootPrimaryGroupedChannel.pairEquiv security).symm roots, primaryColor) = source ↔
        primaryColor = source.2 := by
      constructor
      · exact congrArg Prod.snd
      · intro hp
        exact Prod.ext (hroot.mpr hr) hp
    simp only [RootMassColumns.fiber, if_pos hr, Pi.single_apply, hpair]
  · have hpair : ((RootPrimaryGroupedChannel.pairEquiv security).symm roots, primaryColor) ≠ source := by
      intro h
      exact hr (hroot.mp (congrArg Prod.fst h))
    simp only [RootMassColumns.fiber, if_neg hr, Pi.single_eq_of_ne hpair, Pi.zero_apply]
open _root_.P2M9e1cfc64 renaming h512 → _p2mH512
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h510 (security : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : Palette security → ℝ) :
    RootTaggedSelectedChannel.controlCenterLinear security (RootMassColumns.fiber roots score) =
      RootMassColumns.fiber roots (centerLinear (primaryLaw security) score) := by
  funext other primaryColor
  change centerLinear (primaryLaw security) (RootMassColumns.fiber roots score other) primaryColor = _
  by_cases hequal : other = roots
  · subst other
    simp [RootMassColumns.fiber]
  · simp [RootMassColumns.fiber, hequal, map_zero]
open _root_.P2M9e1cfc64 renaming h510 → _p2mH510
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h511 (security order : ℕ) (source : RootPrimaryGroupedChannel.Input security) :
    RootTaggedSelectedChannel.channel security order
      (RootPrimaryGroupedChannel.pairLinear security (Pi.single source 1)) =
      ((rootReference security).weight (source.1 0) * (rootReference security).weight (source.1 1)) •
        primaryAt security order (RootPrimaryGroupedChannel.pairEquiv security source.1) source.2 := by
  change RootTaggedSelectedChannel.responseLinear security order
    (RootTaggedSelectedChannel.controlCenterLinear security
      (RootTaggedSelectedChannel.curryLinear security
        (RootPrimaryGroupedChannel.pairLinear security (Pi.single source 1)))) = _
  rw [_p2mH512, _p2mH510, _p2mH491,
    _p2mH492]
  rfl
open _root_.P2M9e1cfc64 renaming h511 → _p2mH511
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h502 (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    SelectedOrdinaryRoot.controlCenterLinear security (ordinaryFiber security root score) =
      ordinaryFiber security root (centerLinear (bodyReference security) score) := by
  funext sample
  change centerLinear (bodyReference security) (RootMassColumns.fiber root score sample.1) sample.2 = _
  by_cases hequal : sample.1 = root
  · simp [RootMassColumns.fiber, ordinaryFiber, hequal]
  · simp [RootMassColumns.fiber, ordinaryFiber, hequal, map_zero]
open _root_.P2M9e1cfc64 renaming h502 → _p2mH502
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h508 (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    SelectedOrdinaryRoot.densityLinear security (ordinaryFiber security root score) =
      (rootReference security).weight root • ordinaryDensityAt security root score := by
  change PrimaryTensorInverse.densityInverse security
    (RootTaggedLocal.profileDensity security
      (SelectedOrdinaryRoot.rawMassLinear security
        (SelectedOrdinaryRoot.controlCenterLinear security (ordinaryFiber security root score)))) = _
  rw [_p2mH502]
  unfold ordinaryFiber
  rw [_p2mH488, map_smul, map_smul]
  rfl
open _root_.P2M9e1cfc64 renaming h508 → _p2mH508
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h503 (security order : ℕ) (horder : 1 ≤ order) (root : Root security)
    (score : SafePalette security → ℝ) :
    SelectedOrdinaryRoot.channel security order horder (ordinaryFiber security root score) =
      (rootReference security).weight root • ordinaryAt security order horder root score := by
  have hcentered : SelectedOrdinaryRoot.centeredDensityLinear security (ordinaryFiber security root score) =
      (rootReference security).weight root •
        (⟨ordinaryDensityAt security root score, ordinaryDensityAt_mean security root score⟩ :
          LocalRaisingLinear.centeredScores security) := by
    apply Subtype.ext
    exact _p2mH508 security root score
  change LocalRaisingLinear.primaryEmbeddingLinear security order horder
    (SelectedOrdinaryRoot.centeredDensityLinear security (ordinaryFiber security root score)) * _ = _
  rw [hcentered, map_smul, smul_mul_assoc]
  rfl
open _root_.P2M9e1cfc64 renaming h503 → _p2mH503
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h509 (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    SelectedOrdinaryMean.rootMean security (ordinaryFiber security root score) =
      (rootReference security).weight root • score := by
  funext centerColor
  simp [SelectedOrdinaryMean.rootMean, ordinaryFiber, RootMassColumns.fiber, FiniteDist.expectation, ite_apply]
open _root_.P2M9e1cfc64 renaming h509 → _p2mH509
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h506 (security : ℕ) (score : SafePalette security → ℝ) :
    SelectedOrdinaryMean.constantRoot security score = ∑ root, ordinaryFiber security root score := by
  funext sample
  simp [SelectedOrdinaryMean.constantRoot, ordinaryFiber, RootMassColumns.fiber, ite_apply]
open _root_.P2M9e1cfc64 renaming h506 → _p2mH506
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h505 (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    SelectedOrdinaryRoot.channel security order horder (SelectedOrdinaryMean.constantRoot security score) =
      ∑ root, (rootReference security).weight root • ordinaryAt security order horder root score := by
  rw [_p2mH506, map_sum]
  simp only [_p2mH503]
open _root_.P2M9e1cfc64 renaming h505 → _p2mH505
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h499 (security order : ℕ) (horder : 1 ≤ order) (root : Root security)
    (score : SafePalette security → ℝ) :
    SelectedOrdinaryHybrid.channel security order horder (ordinaryFiber security root score) =
      (rootReference security).weight root • hybridAt security order horder root score := by
  have hcenter : SelectedOrdinaryMean.rootCenter security (ordinaryFiber security root score) =
      ordinaryFiber security root score - SelectedOrdinaryMean.constantRoot security
        ((rootReference security).weight root • score) := by
    change ordinaryFiber security root score - SelectedOrdinaryMean.constantRoot security
      (SelectedOrdinaryMean.rootMean security (ordinaryFiber security root score)) = _
    rw [_p2mH509]
  rw [SelectedOrdinaryHybrid.channel_apply, hcenter, _p2mH509, map_smul]
  rw [map_sub, map_smul, map_smul, _p2mH503, _p2mH505]
  unfold hybridAt
  rw [smul_sub, smul_add]
  abel
open _root_.P2M9e1cfc64 renaming h499 → _p2mH499
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h514 (security order : ℕ) (horder : 1 ≤ order)
    (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (root : Root security) :
    RootTaggedFamilies.rootFamilyLinear security order horder role queue (Pi.single root 1) =
      (rootReference security).weight root • singletonFirstAt security order horder role queue root := by
  have hlift : RootTaggedLocal.rootLift security role queue (Pi.single root 1) =
      (rootReference security).weight root • singletonDensityAt security role queue root := by
    rw [RootTaggedLocal.rootLift_apply, _p2mH493, map_smul, map_smul]
    rfl
  have hs : (⟨RootTaggedLocal.rootLift security role queue (Pi.single root 1),
      RootTaggedLocal.rootLift_mean security role queue (Pi.single root 1)⟩ : LocalRaisingLinear.centeredScores security) =
      (rootReference security).weight root •
        (⟨singletonDensityAt security role queue root, singletonDensityAt_mean security role queue root⟩ :
          LocalRaisingLinear.centeredScores security) := by
    apply Subtype.ext
    exact hlift
  rw [RootTaggedFamilies.rootFamilyLinear_apply]
  change LocalRaisingLinear.primaryEmbeddingLinear security order horder
    (⟨RootTaggedLocal.rootLift security role queue (Pi.single root 1),
      RootTaggedLocal.rootLift_mean security role queue (Pi.single root 1)⟩ : LocalRaisingLinear.centeredScores security) = _
  rw [hs, map_smul]
  rfl
open _root_.P2M9e1cfc64 renaming h514 → _p2mH514
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h513 (security order : ℕ) (horder : 1 ≤ order)
    (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (root : Root security) :
    RootUnselectedChannels.singletonChannel security order horder role queue (Pi.single root 1) =
      (rootReference security).weight root • singletonAt security order horder role queue root := by
  change RootTaggedFamilies.rootFamilyLinear security order horder role queue (Pi.single root 1) * _ = _
  rw [_p2mH514, smul_mul_assoc]
  rfl
open _root_.P2M9e1cfc64 renaming h513 → _p2mH513
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h501 (security order : ℕ) (root : Root security) :
    RootLegCoefficientLinear.rootHigherLinear security order (Pi.single root 1) =
      (rootReference security).weight root • legHigherAt security order root := by
  change RootLegCoefficientLinear.higherFamilyLinear security order
    (RootTaggedLegHigher.massLinear security (Pi.single root 1)) = _
  rw [_p2mH486, map_smul]
  rfl
open _root_.P2M9e1cfc64 renaming h501 → _p2mH501
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h500 (security order : ℕ) (horder : 1 ≤ order) (root : Root security) :
    RootUnselectedChannels.legChannel security order horder (Pi.single root 1) =
      (rootReference security).weight root • legAt security order horder root := by
  change (RootTaggedFamilies.rootFamilyLinear security order horder .attachment 0 (Pi.single root 1) +
    RootLegCoefficientLinear.rootHigherLinear security order (Pi.single root 1)) * _ = _
  rw [_p2mH514, _p2mH501, ← smul_add, smul_mul_assoc]
  rfl
open _root_.P2M9e1cfc64 renaming h500 → _p2mH500
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h516 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : ActualBlockFock.BlockIndex security) (root : Root security) :
    RootUnselectedBlockChannel.channel security order horder queue block (Pi.single root 1) =
      (rootReference security).weight root • unselectedAt security order horder queue block root := by
  rcases block with leg | single
  · exact _p2mH500 security order horder root
  · rcases single with center | point
    · exact _p2mH513 security order horder .free 0 root
    · exact _p2mH513 security order horder .queue queue root
open _root_.P2M9e1cfc64 renaming h516 → _p2mH516
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h507 (security : ℕ) (source : RootOrdinaryGroupedChannel.Input security) :
    RootOrdinaryGroupedChannel.toRaw security (Pi.single source 1) =
      ordinaryFiber security (source.1 0) (Pi.single source.2 1) := by
  funext sample
  change (Pi.single (M := fun _ : RootOrdinaryGroupedChannel.Input security => ℝ) source 1)
    ((fun _ => sample.1), sample.2) = _
  have hroots : (fun _ : Fin 1 => sample.1) = source.1 ↔ sample.1 = source.1 0 := by
    constructor
    · intro h
      exact congrFun h 0
    · intro h
      funext index
      rw [Fin.eq_zero index]
      exact h
  have hpair : ((fun _ : Fin 1 => sample.1), sample.2) = source ↔
      sample.1 = source.1 0 ∧ sample.2 = source.2 := by
    rw [Prod.ext_iff, hroots]
  by_cases hr : sample.1 = source.1 0
  · have hpair' : ((fun _ : Fin 1 => sample.1), sample.2) = source ↔ sample.2 = source.2 := by
      constructor
      · intro h
        exact (hpair.mp h).2
      · intro h
        exact hpair.mpr ⟨hr, h⟩
    simp only [ordinaryFiber, RootMassColumns.fiber, if_pos hr, Pi.single_apply, hpair']
  · have hpair' : ((fun _ : Fin 1 => sample.1), sample.2) ≠ source := fun h => hr (hpair.mp h).1
    simp only [ordinaryFiber, RootMassColumns.fiber, if_neg hr, Pi.zero_apply, Pi.single_eq_of_ne hpair']
open _root_.P2M9e1cfc64 renaming h507 → _p2mH507
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h504 (security order : ℕ) (horder : 1 ≤ order) (source : RootOrdinaryGroupedChannel.Input security) :
    SelectedOrdinaryHybrid.channel security order horder
      (RootOrdinaryGroupedChannel.toRaw security (Pi.single source 1)) =
      (rootReference security).weight (source.1 0) •
        hybridAt security order horder (source.1 0) (Pi.single source.2 1) := by
  rw [_p2mH507]
  exact _p2mH499 security order horder _ _
open _root_.P2M9e1cfc64 renaming h504 → _p2mH504
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h517 (security : ℕ) (source : RootUnselectedGrouped.Input security) :
    RootUnselectedGrouped.extractLinear security (Pi.single source 1) = Pi.single (source.1 0) 1 := by
  funext root
  change (Pi.single (M := fun _ : RootUnselectedGrouped.Input security => ℝ) source 1)
    ((RootUnselectedGrouped.inputEquiv security).symm root) = _
  have hequal : (RootUnselectedGrouped.inputEquiv security).symm root = source ↔ root = source.1 0 := by
    constructor
    · intro h
      have h' := congrArg (RootUnselectedGrouped.inputEquiv security) h
      calc
        root = RootUnselectedGrouped.inputEquiv security source := by
          simpa only [Equiv.apply_symm_apply] using h'
        _ = source.1 0 := rfl
    · intro h
      change _ = _
      rw [show source.1 0 = RootUnselectedGrouped.inputEquiv security source from rfl] at h
      rw [h, Equiv.symm_apply_apply]
  simp only [Pi.single_apply, hequal]
open _root_.P2M9e1cfc64 renaming h517 → _p2mH517
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h518 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : ActualBlockFock.BlockIndex security) (source : RootUnselectedGrouped.Input security) :
    RootUnselectedGrouped.channel security order horder queue block (Pi.single source 1) =
      (rootReference security).weight (source.1 0) • unselectedAt security order horder queue block (source.1 0) := by
  change RootUnselectedBlockChannel.channel security order horder queue block
    (RootUnselectedGrouped.extractLinear security (Pi.single source 1)) = _
  rw [_p2mH517]
  exact _p2mH516 security order horder queue block _
open _root_.P2M9e1cfc64 renaming h518 → _p2mH518
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h515 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : TaggedSelection.Selection security r s) (tagged : Finset (ActualBlockFock.BlockIndex security))
    (group : PairedRootPlacement.ActiveGroup selection tagged)
    (source : ActualRootGroupedChannel.Input selection tagged group) :
    ActualRootProjectionData.unprojectedChannel order horder queue selection tagged group (Pi.single source 1) =
      (∏ slot, (rootReference security).weight (source.1 slot)) •
        reducedColumn order horder queue selection tagged group source := by
  rcases group with (primary | ordinary) | kept
  · have hprod : (∏ slot, (rootReference security).weight (source.1 slot)) =
        (rootReference security).weight (source.1 (0 : Fin 2)) * (rootReference security).weight (source.1 (1 : Fin 2)) := by
      calc
        _ = ∏ slot : Fin 2, (rootReference security).weight (source.1 slot) :=
          Finset.prod_congr (by ext; simp) (fun _ _ => rfl)
        _ = _ := Fin.prod_univ_two _
    rw [hprod]
    exact _p2mH511 security order source
  · have hprod : (∏ slot, (rootReference security).weight (source.1 slot)) =
        (rootReference security).weight (source.1 (0 : Fin 1)) := by
      calc
        _ = ∏ slot : Fin 1, (rootReference security).weight (source.1 slot) :=
          Finset.prod_congr (by
            ext index
            have hi : (index : Fin 1) = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance index 0
            subst index
            simp) (fun _ _ => rfl)
        _ = _ := Fin.prod_univ_one _
    rw [hprod]
    exact _p2mH504 security order horder source
  · have hprod : (∏ slot, (rootReference security).weight (source.1 slot)) =
        (rootReference security).weight (source.1 (0 : Fin 1)) := by
      calc
        _ = ∏ slot : Fin 1, (rootReference security).weight (source.1 slot) :=
          Finset.prod_congr (by
            ext index
            have hi : (index : Fin 1) = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance index 0
            subst index
            simp) (fun _ _ => rfl)
        _ = _ := Fin.prod_univ_one _
    rw [hprod]
    have hdelta : (Pi.single (M := fun _ : ActualRootGroupedChannel.Input selection tagged (.inr kept) => ℝ) source 1) =
        (Pi.single (M := fun _ : RootUnselectedGrouped.Input security => ℝ) source 1) := by
      funext word
      by_cases hequal : word = source <;> simp only [Pi.single_apply, hequal, if_true, if_false]
    rw [hdelta]
    exact _p2mH518 security order horder queue kept.val.val source
open _root_.P2M9e1cfc64 renaming h515 → _p2mH515
end
open _root_.P2M9e1cfc64 renaming h499 → _p2mH499
open _root_.P2M9e1cfc64 renaming h500 → _p2mH500
open _root_.P2M9e1cfc64 renaming h501 → _p2mH501
open _root_.P2M9e1cfc64 renaming h502 → _p2mH502
open _root_.P2M9e1cfc64 renaming h503 → _p2mH503
open _root_.P2M9e1cfc64 renaming h504 → _p2mH504
open _root_.P2M9e1cfc64 renaming h505 → _p2mH505
open _root_.P2M9e1cfc64 renaming h506 → _p2mH506
open _root_.P2M9e1cfc64 renaming h507 → _p2mH507
open _root_.P2M9e1cfc64 renaming h508 → _p2mH508
open _root_.P2M9e1cfc64 renaming h509 → _p2mH509
open _root_.P2M9e1cfc64 renaming h510 → _p2mH510
open _root_.P2M9e1cfc64 renaming h511 → _p2mH511
open _root_.P2M9e1cfc64 renaming h512 → _p2mH512
open _root_.P2M9e1cfc64 renaming h513 → _p2mH513
open _root_.P2M9e1cfc64 renaming h514 → _p2mH514
open _root_.P2M9e1cfc64 renaming h515 → _p2mH515
open _root_.P2M9e1cfc64 renaming h516 → _p2mH516
open _root_.P2M9e1cfc64 renaming h517 → _p2mH517
open _root_.P2M9e1cfc64 renaming h518 → _p2mH518
end CurrentAFT.RootReferenceColumns
open _root_.P2M9e1cfc64 renaming h499 → _p2mH499
open _root_.P2M9e1cfc64 renaming h500 → _p2mH500
open _root_.P2M9e1cfc64 renaming h501 → _p2mH501
open _root_.P2M9e1cfc64 renaming h502 → _p2mH502
open _root_.P2M9e1cfc64 renaming h503 → _p2mH503
open _root_.P2M9e1cfc64 renaming h504 → _p2mH504
open _root_.P2M9e1cfc64 renaming h505 → _p2mH505
open _root_.P2M9e1cfc64 renaming h506 → _p2mH506
open _root_.P2M9e1cfc64 renaming h507 → _p2mH507
open _root_.P2M9e1cfc64 renaming h508 → _p2mH508
open _root_.P2M9e1cfc64 renaming h509 → _p2mH509
open _root_.P2M9e1cfc64 renaming h510 → _p2mH510
open _root_.P2M9e1cfc64 renaming h511 → _p2mH511
open _root_.P2M9e1cfc64 renaming h512 → _p2mH512
open _root_.P2M9e1cfc64 renaming h513 → _p2mH513
open _root_.P2M9e1cfc64 renaming h514 → _p2mH514
open _root_.P2M9e1cfc64 renaming h515 → _p2mH515
open _root_.P2M9e1cfc64 renaming h516 → _p2mH516
open _root_.P2M9e1cfc64 renaming h517 → _p2mH517
open _root_.P2M9e1cfc64 renaming h518 → _p2mH518
end
open _root_.P2M9e1cfc64 renaming h502 → _p2mH502
open _root_.P2M9e1cfc64 renaming h516 → _p2mH516
open _root_.P2M9e1cfc64 renaming h515 → _p2mH515
open _root_.P2M9e1cfc64 renaming h501 → _p2mH501
open _root_.P2M9e1cfc64 renaming h512 → _p2mH512
open _root_.P2M9e1cfc64 renaming h507 → _p2mH507
open _root_.P2M9e1cfc64 renaming h509 → _p2mH509
open _root_.P2M9e1cfc64 renaming h499 → _p2mH499
open _root_.P2M9e1cfc64 renaming h508 → _p2mH508
open _root_.P2M9e1cfc64 renaming h505 → _p2mH505
open _root_.P2M9e1cfc64 renaming h511 → _p2mH511
open _root_.P2M9e1cfc64 renaming h514 → _p2mH514
open _root_.P2M9e1cfc64 renaming h518 → _p2mH518
open _root_.P2M9e1cfc64 renaming h513 → _p2mH513
open _root_.P2M9e1cfc64 renaming h503 → _p2mH503
open _root_.P2M9e1cfc64 renaming h517 → _p2mH517
open _root_.P2M9e1cfc64 renaming h504 → _p2mH504
open _root_.P2M9e1cfc64 renaming h506 → _p2mH506
open _root_.P2M9e1cfc64 renaming h510 → _p2mH510
open _root_.P2M9e1cfc64 renaming h500 → _p2mH500
section
namespace CurrentAFT.RootWeightedSynthesis
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  CycleRootExpansion ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootWeightedSynthesis.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootWeightedSynthesis.nativeVertexDecidableEq
attribute [local instance] _root_.CurrentAFT.RootWeightedSynthesis.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RootWeightedSynthesis.classicalProdDecidableEq
attribute [local instance] _root_.CurrentAFT.RootWeightedSynthesis.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h536 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : GroupInput selection tagged) :
    (∏ group, ∏ slot, (rootReference security).weight ((source group).1 slot)) =
      (∏ index, (rootReference security).weight (taggedOutput selection tagged source index)) *
        untaggedWeight selection tagged source := by
  have h := Finset.prod_mul_prod_compl (Finset.univ.map (sourceEmbedding selection tagged))
    (fun slot : RootSlot selection tagged => (rootReference security).weight ((source slot.fst).1 slot.snd))
  simpa only [Finset.prod_map, Fintype.prod_sigma, taggedOutput, untaggedWeight] using h.symm
open _root_.P2M9e1cfc64 renaming h536 → _p2mH536
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h538 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (source : GroupInput selection tagged) :
    jointInput selection tagged layout kernel source *
        (∏ group, ∏ slot, (rootReference security).weight ((source group).1 slot)) =
      controlKernel selection tagged kernel (fun group => (source group).2) *
        untaggedWeight selection tagged source * weightedCoefficient selection tagged layout source := by
  letI : DecidableEq (Fin tagged.card) := instDecidableEqFin _
  have h := _p2mH519 security tagged.card (labels tagged layout)
    (taggedOutput selection tagged source)
  rw [FiniteDist.expectation_map] at h
  change (∏ index, (rootReference security).weight (taggedOutput selection tagged source index)) *
    selectedCoefficient security tagged.card (labels tagged layout) (taggedOutput selection tagged source) =
      weightedCoefficient selection tagged layout source at h
  rw [← h, _p2mH536]
  unfold jointInput
  change selectedCoefficient security tagged.card (labels tagged layout) (taggedOutput selection tagged source) * _ * _ = _
  ring
open _root_.P2M9e1cfc64 renaming h538 → _p2mH538
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h537 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    ActualRootResponse.response order horder queue selection tagged layout kernel =
      ∑ source : GroupInput selection tagged,
        (controlKernel selection tagged kernel (fun group => (source group).2) *
          untaggedWeight selection tagged source * weightedCoefficient selection tagged layout source) •
            ∏ group, RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group) := by
  rw [_p2mH40, GroupedFamilyIdentity.response_eq]
  apply Finset.sum_congr rfl
  intro source _
  have hcolumn (group : ActiveGroup selection tagged) :
      ActualRootProjectionData.unprojectedChannel order horder queue selection tagged group
        (@Pi.single (ActualRootGroupedChannel.Input selection tagged group) (fun _ => ℝ) (fun _ => Real.instZero)
          (Classical.decEq _) (source group) 1) =
        (∏ slot, (rootReference security).weight ((source group).1 slot)) •
          RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group) := by
    convert _p2mH515 order horder queue selection tagged group (source group) using 1
    congr 1
    funext word
    by_cases hequal : word = source group <;> simp only [Pi.single_apply, hequal, if_true, if_false]
  simp_rw [hcolumn, Finset.prod_smul, smul_smul]
  rw [_p2mH538]
open _root_.P2M9e1cfc64 renaming h537 → CurrentAFT.RootWeightedSynthesis.response_eq
open _root_.P2M9e1cfc64 renaming h537 → _p2mH537
end
open _root_.P2M9e1cfc64 renaming h536 → _p2mH536
open _root_.P2M9e1cfc64 renaming h537 → CurrentAFT.RootWeightedSynthesis.response_eq
open _root_.P2M9e1cfc64 renaming h537 → _p2mH537
open _root_.P2M9e1cfc64 renaming h538 → _p2mH538
end CurrentAFT.RootWeightedSynthesis
open _root_.P2M9e1cfc64 renaming h536 → _p2mH536
open _root_.P2M9e1cfc64 renaming h537 → CurrentAFT.RootWeightedSynthesis.response_eq
open _root_.P2M9e1cfc64 renaming h537 → _p2mH537
open _root_.P2M9e1cfc64 renaming h538 → _p2mH538
end
open _root_.P2M9e1cfc64 renaming h536 → _p2mH536
open _root_.P2M9e1cfc64 renaming h538 → _p2mH538
open _root_.P2M9e1cfc64 renaming h537 → CurrentAFT.RootWeightedSynthesis.response_eq
open _root_.P2M9e1cfc64 renaming h537 → _p2mH537
section
namespace CurrentAFT.CurrentGroupSourcePadding
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  GroupSourcePadding CurrentRectangleIndex
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.CurrentGroupSourcePadding.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.CurrentGroupSourcePadding.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.CurrentGroupSourcePadding.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h61 {Scalar : Type*} [AddCommMonoid Scalar] {security r s k : ℕ}
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (keptOrdering : Fin k ≃ HitKept selection tagged) (summand : GroupInput selection tagged → Scalar) :
    (∑ index : Fin ((colors security)^(((r+s)+k)*3)),
      (decode selection tagged keptOrdering index).elim 0 summand) = ∑ source, summand source := by
  have h := _p2mH90 (colors security) (colors_pos security) (safe security) (groupKind selection tagged)
    ((r+s)+k) (groupOrdering selection tagged keptOrdering) (summand ∘ sourceEquiv selection tagged)
  simpa only [decode, Option.elim_map, Function.comp_apply,
    Equiv.sum_comp (sourceEquiv selection tagged)] using h
open _root_.P2M9e1cfc64 renaming h61 → _p2mH61
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h60 {security r s k : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (keptOrdering : Fin k ≃ HitKept selection tagged)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : ControlCoordinates.canonicalKernels (ProposalPrimary.primaryLaw security)
      (ActualControls.bodyReference security) r s) :
    ActualRootResponse.response order horder queue selection tagged layout kernel =
      ∑ index : Fin ((colors security)^(((r+s)+k)*3)),
        (decode selection tagged keptOrdering index).elim 0 (fun source =>
          (controlKernel selection tagged kernel (fun group => (source group).2) *
            RootWeightedSynthesis.untaggedWeight selection tagged source *
            RootWeightedSynthesis.weightedCoefficient selection tagged layout source) •
            ∏ group, RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group)) := by
  rw [_p2mH61, _p2mH537]
open _root_.P2M9e1cfc64 renaming h60 → CurrentAFT.CurrentGroupSourcePadding.response_eq
open _root_.P2M9e1cfc64 renaming h60 → _p2mH60
end
open _root_.P2M9e1cfc64 renaming h60 → CurrentAFT.CurrentGroupSourcePadding.response_eq
open _root_.P2M9e1cfc64 renaming h60 → _p2mH60
open _root_.P2M9e1cfc64 renaming h61 → _p2mH61
end CurrentAFT.CurrentGroupSourcePadding
open _root_.P2M9e1cfc64 renaming h60 → CurrentAFT.CurrentGroupSourcePadding.response_eq
open _root_.P2M9e1cfc64 renaming h60 → _p2mH60
open _root_.P2M9e1cfc64 renaming h61 → _p2mH61
end
open _root_.P2M9e1cfc64 renaming h61 → _p2mH61
open _root_.P2M9e1cfc64 renaming h60 → CurrentAFT.CurrentGroupSourcePadding.response_eq
open _root_.P2M9e1cfc64 renaming h60 → _p2mH60
section
namespace CurrentAFT.CurrentRootSlotIndex
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h62 {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (tag : tagged) :
    tagPosition selection tagged ordering tag =
      (ordering.symm (tagEmbedding selection tagged tag).fst,
        slotNumber selection tagged (tagEmbedding selection tagged tag)) := by
  unfold tagPosition
  simp only [position_tag, Option.get_some, encode, Equiv.symm_apply_apply]
open _root_.P2M9e1cfc64 renaming h62 → _p2mH62
end CurrentAFT.CurrentRootSlotIndex
open _root_.P2M9e1cfc64 renaming h62 → _p2mH62
end
open _root_.P2M9e1cfc64 renaming h62 → _p2mH62
section
namespace CurrentAFT.RationalFirstResponseProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  DiffuseProfiles.actualProfile DiffuseProfiles.signProfile DiffuseProfiles.activation
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h225 (colors width output : ℕ) (positive : Bool) (blur source : ℤ) :
    |(profileKernel colors width positive blur source output : ℝ)| ≤ 1 :=
  _p2mH19 _ _ _ _ _ _
open _root_.P2M9e1cfc64 renaming h225 → _p2mH225
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h227 (security : ℕ) (positive : Bool) (output : FirstHistogram.Palette security) :
    (actualSeedLaw security).expectation (fun seed =>
      (profileKernel (Parameters.modulus security) (Parameters.anchorWidth security) positive
        (actualBlur security seed) (actualSecond security seed) output.val : ℝ)) = actualProfile security positive output := by
  simp only [profileKernel, AFT.V7Calibration.averagedSliceProgram_cast, actualProfile, DiffuseProfiles.profile,
    TrimmedSlice.mixedLaw, FiniteDist.expectation, intervalStart]
open _root_.P2M9e1cfc64 renaming h227 → _p2mH227
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h226 (security bits : ℕ) (positive : Bool) (output : FirstHistogram.Palette security) :
    |(profile security bits positive output.val : ℝ)-actualProfile security positive output| ≤ 3/(2:ℝ)^bits := by
  have hw : (security+2)^48 = Parameters.anchorWidth security := by
    simp only [anchorWidth_eq, Parameters.base]
  have he : (profile security bits positive output.val : ℝ) =
      (approximateSeedLaw security bits).expectation (fun seed =>
        (profileKernel (Parameters.modulus security) (Parameters.anchorWidth security) positive
          (actualBlur security seed) (actualSecond security seed) output.val : ℝ)) := by
    unfold profile
    rw [seedEvaluate_cast, PublicParameterProgram.modulus_value, hw]
    rfl
  calc
    _ = |(approximateSeedLaw security bits).expectation (fun seed =>
        (profileKernel (Parameters.modulus security) (Parameters.anchorWidth security) positive
          (actualBlur security seed) (actualSecond security seed) output.val : ℝ)) -
      (actualSeedLaw security).expectation (fun seed =>
        (profileKernel (Parameters.modulus security) (Parameters.anchorWidth security) positive
          (actualBlur security seed) (actualSecond security seed) output.val : ℝ))| :=
      congrArg abs (congrArg₂ (·-·) he (_p2mH227 security positive output).symm)
    _ ≤ _ := (_p2mH70 _ _ _ 1
      (fun seed => _p2mH225 _ _ _ _ _ _)).trans (by simpa only [one_mul] using _p2mH393 security bits)
open _root_.P2M9e1cfc64 renaming h226 → _p2mH226
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h216 (security : ℕ) (positive : Bool) (output : FirstHistogram.Palette security) :
    |actualProfile security positive output| ≤ 1 := by
  rw [← _p2mH227]
  unfold FiniteDist.expectation
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ seed : ActualSeed security, (actualSeedLaw security).weight seed := by
      apply Finset.sum_le_sum
      intro seed _
      rw [abs_mul, abs_of_nonneg ((actualSeedLaw security).nonneg seed)]
      exact (mul_le_mul_of_nonneg_left (_p2mH225 _ _ _ _ _ _)
        ((actualSeedLaw security).nonneg seed)).trans_eq (mul_one _)
    _ = 1 := (actualSeedLaw security).sum_one
open _root_.P2M9e1cfc64 renaming h216 → _p2mH216
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h228 (security bits : ℕ) (output : FirstHistogram.Palette security) :
    |(signProfile security bits output.val : ℝ)-DiffuseProfiles.signProfile security output| ≤ 7/(2:ℝ)^bits := by
  let rate : ℝ := LocalPairProgram.activationApprox security bits
  let first : ℝ := profile security bits true output.val
  let second : ℝ := profile security bits false output.val
  let trueFirst := actualProfile security true output
  let trueSecond := actualProfile security false output
  have hr := LocalPairProgram.activationApprox_bounds security bits
  have hrate : 0 ≤ rate ∧ rate ≤ 1/2 := hr
  have hrem : 0 ≤ 1-rate := by linarith only [hrate.2]
  have hrem' : 1-rate ≤ 1 := by linarith only [hrate.1]
  have he := _p2mH130 security bits
  have hp : |first-trueFirst| ≤ 3/(2:ℝ)^bits := _p2mH226 security bits true output
  have hm : |second-trueSecond| ≤ 3/(2:ℝ)^bits := _p2mH226 security bits false output
  have hd : |(first-trueFirst)-(second-trueSecond)| ≤ 6/(2:ℝ)^bits :=
    (abs_sub _ _).trans ((add_le_add hp hm).trans_eq (by ring))
  have hg : |trueFirst-trueSecond| ≤ 2 :=
    (abs_sub _ _).trans (by linarith only [_p2mH216 security true output, _p2mH216 security false output])
  unfold signProfile DiffuseProfiles.signProfile
  simp only [Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
  change |(1-rate)*(first-second)-(1-DiffuseProfiles.activation security)*(trueFirst-trueSecond)| ≤ _
  calc
    _ = |(1-rate)*((first-trueFirst)-(second-trueSecond)) +
        (DiffuseProfiles.activation security-rate)*(trueFirst-trueSecond)| := by congr 1; ring
    _ ≤ |(1-rate)*((first-trueFirst)-(second-trueSecond))| +
        |(DiffuseProfiles.activation security-rate)*(trueFirst-trueSecond)| := abs_add_le _ _
    _ = (1-rate)*|(first-trueFirst)-(second-trueSecond)| +
        |rate-DiffuseProfiles.activation security| * |trueFirst-trueSecond| := by
      rw [abs_mul, abs_of_nonneg hrem, abs_mul, abs_sub_comm (DiffuseProfiles.activation security) rate]
    _ ≤ 1*(6/(2:ℝ)^bits)+((1/2:ℝ)*(1/(2:ℝ)^bits))*2 :=
      add_le_add (mul_le_mul hrem' hd (abs_nonneg _) (by positivity))
        (mul_le_mul he hg (abs_nonneg _) (by positivity))
    _ = _ := by ring
open _root_.P2M9e1cfc64 renaming h228 → _p2mH228
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h218 (security : ℕ) (color : FirstHistogram.Palette security) :
    (anchorSign security color.val : ℝ) = FirstResponse.anchorSign security color := by
  unfold anchorSign FirstResponse.anchorSign
  rw [PublicParameterProgram.modulus_value]
  split_ifs <;> norm_num
open _root_.P2M9e1cfc64 renaming h218 → _p2mH218
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h222 (security : ℕ) (input : ℕ → ℚ) :
    (functional security input : ℝ) =
      AFT.signFunctional (FirstResponse.anchorSign security) (fun color : FirstHistogram.Palette security => (input color.val : ℝ)) := by
  simp only [functional, Rat.cast_sum, Rat.cast_mul]
  rw [PublicParameterProgram.modulus_value]
  simp only [_p2mH218, AFT.signFunctional]
open _root_.P2M9e1cfc64 renaming h222 → _p2mH222
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h219 (security bits : ℕ) :
    |(denominator security bits : ℝ)-actualDenominator security| ≤
      (8*(Parameters.modulus security:ℝ)+1)/(2:ℝ)^bits := by
  have ha := _p2mH130 security bits
  have hs : |AFT.signFunctional (FirstResponse.anchorSign security)
      (fun color => (signProfile security bits color.val : ℝ))-
      AFT.signFunctional (FirstResponse.anchorSign security) (DiffuseProfiles.signProfile security)| ≤
      (Parameters.modulus security:ℝ)*(7/(2:ℝ)^bits) := by
    unfold AFT.signFunctional
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _color : FirstHistogram.Palette security, 7/(2:ℝ)^bits := by
        apply Finset.sum_le_sum
        intro color _
        rw [← mul_sub, abs_mul]
        exact (mul_le_mul (FirstResponse.anchorSign_abs_le_one security color)
          (_p2mH228 security bits color) (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
      _ = _ := by simp
  unfold denominator actualDenominator
  rw [Rat.cast_add, _p2mH222]
  calc
    _ = |((LocalPairProgram.activationApprox security bits : ℝ)-DiffuseProfiles.activation security) +
        (AFT.signFunctional (FirstResponse.anchorSign security) (fun color => (signProfile security bits color.val : ℝ))-
          AFT.signFunctional (FirstResponse.anchorSign security) (DiffuseProfiles.signProfile security))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add ha hs)
    _ = ((1/2:ℝ)+7*Parameters.modulus security)/(2:ℝ)^bits := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by have hq := FirstResponse.modulus_pos security; linarith) (by positivity)
open _root_.P2M9e1cfc64 renaming h219 → _p2mH219
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h220 (security bits : ℕ) (hprecision : PrecisionBudget security bits) :
    1/(16*(Parameters.base security:ℝ)) ≤ (denominator security bits : ℝ) := by
  have hb := FirstResponse.base_pos security
  have ha := FirstResponse.activation_lower_simple security
  have hd := _p2mH84 security
  change DiffuseProfiles.activation security/2 ≤ actualDenominator security at hd
  have he := _p2mH219 security bits
  have he' : |(denominator security bits : ℝ)-actualDenominator security| ≤
      (8*(Parameters.modulus security:ℝ)+1)*(1/(2:ℝ)^bits) := he.trans_eq (by ring)
  have hprec : (8*(Parameters.modulus security:ℝ)+2)*(1/(2:ℝ)^bits) ≤
      1/(16*(Parameters.base security:ℝ)) := hprecision
  have hal : 1/(8*(Parameters.base security:ℝ)) ≤ actualDenominator security :=
    (show 1/(8*(Parameters.base security:ℝ)) ≤ DiffuseProfiles.activation security/2 by
      convert div_le_div_of_nonneg_right ha (by norm_num : (0:ℝ) ≤ 2) using 1 <;> first | rfl | ring).trans hd
  have hlow := (abs_le.mp he').1
  have heps : 0 ≤ 1/(2:ℝ)^bits := by positivity
  have hscale : 1/(8*(Parameters.base security:ℝ)) = 2*(1/(16*(Parameters.base security:ℝ))) := by ring
  nlinarith only [hal, hlow, hprec, heps, hscale]
open _root_.P2M9e1cfc64 renaming h220 → _p2mH220
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h223 (security bits : ℕ) (hprecision : PrecisionBudget security bits) :
    guardedDenominator security bits = denominator security bits := by
  have hd := _p2mH84 security
  change DiffuseProfiles.activation security/2 ≤ actualDenominator security at hd
  have ha := FirstResponse.activation_lower_simple security
  have hal : 1/(16*(Parameters.base security:ℝ)) ≤ DiffuseProfiles.activation security/4 := by
    convert div_le_div_of_nonneg_right ha (by norm_num : (0:ℝ) ≤ 4) using 1 <;> first | rfl | ring
  have he := _p2mH219 security bits
  have he' : |(denominator security bits : ℝ)-actualDenominator security| ≤
      (8*(Parameters.modulus security:ℝ)+1)*(1/(2:ℝ)^bits) := he.trans_eq (by ring)
  have hae := _p2mH130 security bits
  have hprec : (8*(Parameters.modulus security:ℝ)+2)*(1/(2:ℝ)^bits) ≤
      1/(16*(Parameters.base security:ℝ)) := hprecision
  have hguard : (LocalPairProgram.activationApprox security bits : ℝ)/4 ≤ (denominator security bits : ℝ) := by
    have hlow := (abs_le.mp he').1
    have hhigh := (abs_le.mp hae).2
    have heps : 0 ≤ 1/(2:ℝ)^bits := by positivity
    nlinarith only [hd, hal, hprec, hlow, hhigh, heps]
  have hguardQ : LocalPairProgram.activationApprox security bits/4 ≤ denominator security bits := by
    exact_mod_cast hguard
  exact max_eq_left hguardQ
open _root_.P2M9e1cfc64 renaming h223 → _p2mH223
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h215 (security : ℕ) :
    1/(16*(Parameters.base security:ℝ)) ≤ actualDenominator security := by
  have ha := FirstResponse.activation_lower_simple security
  have hd := _p2mH84 security
  change DiffuseProfiles.activation security/2 ≤ actualDenominator security at hd
  have hal : 1/(8*(Parameters.base security:ℝ)) ≤ DiffuseProfiles.activation security/2 := by
    convert div_le_div_of_nonneg_right ha (by norm_num : (0:ℝ) ≤ 2) using 1 <;> first | rfl | ring
  apply le_trans _ (hal.trans hd)
  exact one_div_le_one_div_of_le (by have hb := FirstResponse.base_pos security; positivity) (by
    have hb := FirstResponse.base_pos security; nlinarith)
open _root_.P2M9e1cfc64 renaming h215 → _p2mH215
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h221 (security : ℕ) (input : ℕ → ℚ) (bound : ℝ) (_hbound : 0 ≤ bound)
    (hinput : ∀ color : FirstHistogram.Palette security, |(input color.val : ℝ)| ≤ bound) :
    |(functional security input : ℝ)| ≤ (Parameters.modulus security:ℝ)*bound := by
  rw [_p2mH222]
  unfold AFT.signFunctional
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _color : FirstHistogram.Palette security, bound := by
      apply Finset.sum_le_sum
      intro color _
      rw [abs_mul]
      exact (mul_le_mul (FirstResponse.anchorSign_abs_le_one security color) (hinput color)
        (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = _ := by simp
open _root_.P2M9e1cfc64 renaming h221 → _p2mH221
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h217 (security : ℕ) (color : FirstHistogram.Palette security) :
    |DiffuseProfiles.signProfile security color| ≤ 2 := by
  have ha := DiffuseProfiles.activation_pos security
  have hu := DiffuseProfiles.activation_le_half security
  unfold DiffuseProfiles.signProfile
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-DiffuseProfiles.activation security)]
  have hgap : |actualProfile security true color - actualProfile security false color| ≤ 2 :=
    (abs_sub _ _).trans ((add_le_add (_p2mH216 security true color)
      (_p2mH216 security false color)).trans_eq (by norm_num))
  exact (mul_le_mul (by linarith : 1-DiffuseProfiles.activation security ≤ 1)
    hgap (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (by norm_num)
open _root_.P2M9e1cfc64 renaming h217 → _p2mH217
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h224 (security bits : ℕ) (input : ℕ → ℚ) (output : FirstHistogram.Palette security)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hinput : ∀ color : FirstHistogram.Palette security, |(input color.val : ℝ)| ≤ bound)
    (hprecision : PrecisionBudget security bits) :
    |(inverse security bits input output.val : ℝ) -
      (FirstResponse.responseEquiv security).symm
        (fun color : FirstHistogram.Palette security => (input color.val : ℝ)) output| ≤
      inverseErrorConstant security*bound/(2:ℝ)^bits := by
  let d : ℝ := actualDenominator security
  let a : ℝ := denominator security bits
  let r : ℝ := DiffuseProfiles.signProfile security output
  let s : ℝ := signProfile security bits output.val
  let f : ℝ := functional security input
  let base : ℝ := Parameters.base security
  let epsilon : ℝ := 1/(2:ℝ)^bits
  have hb : 0 < base := FirstResponse.base_pos security
  have hlo : 0 < 1/(16*base) := by positivity
  have ha : 1/(16*base) ≤ a := _p2mH220 security bits hprecision
  have hd : 1/(16*base) ≤ d := _p2mH215 security
  have ha0 : 0 < a := hlo.trans_le ha
  have hd0 : 0 < d := hlo.trans_le hd
  have hai : a⁻¹ ≤ 16*base := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le hlo ha
  have hdi : d⁻¹ ≤ 16*base := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le hlo hd
  have he : |a-d| ≤ (8*(Parameters.modulus security:ℝ)+1)*epsilon :=
    (_p2mH219 security bits).trans_eq (by dsimp only [epsilon]; ring)
  have hr : |r| ≤ 2 := _p2mH217 security output
  have hs : |s-r| ≤ 7*epsilon := (_p2mH228 security bits output).trans_eq (by dsimp only [epsilon]; ring)
  have hf : |f| ≤ (Parameters.modulus security:ℝ)*bound := _p2mH221 security input bound hbound hinput
  have hrecip : |a⁻¹-d⁻¹| ≤ 256*base^2*((8*(Parameters.modulus security:ℝ)+1)*epsilon) := by
    calc
      _ = |(d-a)*(a⁻¹*d⁻¹)| := by congr 1; field_simp
      _ = |a-d| * (a⁻¹*d⁻¹) := by
        rw [abs_mul, abs_sub_comm d a, abs_of_pos (mul_pos (inv_pos.mpr ha0) (inv_pos.mpr hd0))]
      _ ≤ ((8*(Parameters.modulus security:ℝ)+1)*epsilon)*((16*base)*(16*base)) :=
        mul_le_mul he (mul_le_mul hai hdi (inv_nonneg.mpr hd0.le) (by positivity))
          (mul_nonneg (inv_nonneg.mpr ha0.le) (inv_nonneg.mpr hd0.le)) (by positivity)
      _ = _ := by ring
  have hratio : |s*a⁻¹-r*d⁻¹| ≤ 7*epsilon*(16*base) +
      2*(256*base^2*((8*(Parameters.modulus security:ℝ)+1)*epsilon)) := by
    calc
      _ = |(s-r)*a⁻¹+r*(a⁻¹-d⁻¹)| := by congr 1; ring
      _ ≤ |(s-r)*a⁻¹|+|r*(a⁻¹-d⁻¹)| := abs_add_le _ _
      _ = |s-r| * a⁻¹+|r| * |a⁻¹-d⁻¹| := by rw [abs_mul, abs_of_pos (inv_pos.mpr ha0), abs_mul]
      _ ≤ _ := add_le_add (mul_le_mul hs hai (inv_nonneg.mpr ha0.le) (by positivity))
        (mul_le_mul hr hrecip (abs_nonneg _) (by norm_num))
  have hformula : (inverse security bits input output.val : ℝ) -
      (FirstResponse.responseEquiv security).symm
        (fun color : FirstHistogram.Palette security => (input color.val : ℝ)) output =
      -f*(s*a⁻¹-r*d⁻¹) := by
    rw [_p2mH85]
    simp only [inverse, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, _p2mH223 security bits hprecision,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← _p2mH222]
    change (input output.val:ℝ)-f/a*s - ((input output.val:ℝ)-d⁻¹*f*r) = _
    ring
  rw [hformula, abs_mul, abs_neg]
  calc
    _ ≤ ((Parameters.modulus security:ℝ)*bound)*(7*epsilon*(16*base) +
        2*(256*base^2*((8*(Parameters.modulus security:ℝ)+1)*epsilon))) :=
      mul_le_mul hf hratio (abs_nonneg _) (by have hq := FirstResponse.modulus_pos security; positivity)
    _ = _ := by unfold inverseErrorConstant; dsimp only [base, epsilon]; ring
open _root_.P2M9e1cfc64 renaming h224 → _p2mH224
attribute [local irreducible] sufficientBits
end
open _root_.P2M9e1cfc64 renaming h215 → _p2mH215
open _root_.P2M9e1cfc64 renaming h216 → _p2mH216
open _root_.P2M9e1cfc64 renaming h217 → _p2mH217
open _root_.P2M9e1cfc64 renaming h218 → _p2mH218
open _root_.P2M9e1cfc64 renaming h219 → _p2mH219
open _root_.P2M9e1cfc64 renaming h220 → _p2mH220
open _root_.P2M9e1cfc64 renaming h221 → _p2mH221
open _root_.P2M9e1cfc64 renaming h222 → _p2mH222
open _root_.P2M9e1cfc64 renaming h223 → _p2mH223
open _root_.P2M9e1cfc64 renaming h224 → _p2mH224
open _root_.P2M9e1cfc64 renaming h225 → _p2mH225
open _root_.P2M9e1cfc64 renaming h226 → _p2mH226
open _root_.P2M9e1cfc64 renaming h227 → _p2mH227
open _root_.P2M9e1cfc64 renaming h228 → _p2mH228
end CurrentAFT.RationalFirstResponseProgram
open _root_.P2M9e1cfc64 renaming h215 → _p2mH215
open _root_.P2M9e1cfc64 renaming h216 → _p2mH216
open _root_.P2M9e1cfc64 renaming h217 → _p2mH217
open _root_.P2M9e1cfc64 renaming h218 → _p2mH218
open _root_.P2M9e1cfc64 renaming h219 → _p2mH219
open _root_.P2M9e1cfc64 renaming h220 → _p2mH220
open _root_.P2M9e1cfc64 renaming h221 → _p2mH221
open _root_.P2M9e1cfc64 renaming h222 → _p2mH222
open _root_.P2M9e1cfc64 renaming h223 → _p2mH223
open _root_.P2M9e1cfc64 renaming h224 → _p2mH224
open _root_.P2M9e1cfc64 renaming h225 → _p2mH225
open _root_.P2M9e1cfc64 renaming h226 → _p2mH226
open _root_.P2M9e1cfc64 renaming h227 → _p2mH227
open _root_.P2M9e1cfc64 renaming h228 → _p2mH228
end
open _root_.P2M9e1cfc64 renaming h224 → _p2mH224
open _root_.P2M9e1cfc64 renaming h218 → _p2mH218
open _root_.P2M9e1cfc64 renaming h216 → _p2mH216
open _root_.P2M9e1cfc64 renaming h215 → _p2mH215
open _root_.P2M9e1cfc64 renaming h227 → _p2mH227
open _root_.P2M9e1cfc64 renaming h221 → _p2mH221
open _root_.P2M9e1cfc64 renaming h228 → _p2mH228
open _root_.P2M9e1cfc64 renaming h226 → _p2mH226
open _root_.P2M9e1cfc64 renaming h225 → _p2mH225
open _root_.P2M9e1cfc64 renaming h220 → _p2mH220
open _root_.P2M9e1cfc64 renaming h223 → _p2mH223
open _root_.P2M9e1cfc64 renaming h222 → _p2mH222
open _root_.P2M9e1cfc64 renaming h217 → _p2mH217
open _root_.P2M9e1cfc64 renaming h219 → _p2mH219
section
namespace CurrentAFT.RationalPairedLiftProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
section Generic
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h357 (primary : FiniteDist Primary) (anchor : Primary → FiniteDist Body)
    (score : Primary → ℝ) (bound : ℝ) (hscore : ∀ color, |score color| ≤ bound) (output : Body) :
    |ControlCoordinates.anchorProfile primary anchor score output| ≤ bound := by
  unfold ControlCoordinates.anchorProfile
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ color, primary.weight color*bound := by
      apply Finset.sum_le_sum
      intro color _
      rw [abs_mul, abs_mul, abs_of_nonneg (primary.nonneg color), abs_of_nonneg ((anchor color).nonneg output)]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (hscore color) (primary.nonneg color))
        ((anchor color).atom_le_one output) ((anchor color).nonneg output)
        (mul_nonneg (primary.nonneg color) ((abs_nonneg _).trans (hscore color)))).trans_eq (mul_one _)
    _ = bound := by rw [← Finset.sum_mul, primary.sum_one, one_mul]
open _root_.P2M9e1cfc64 renaming h357 → _p2mH357
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h358 (primary approximatePrimary : FiniteDist Primary)
    (anchor approximateAnchor : Primary → FiniteDist Body) (score : Primary → ℝ)
    (bound primaryError anchorError : ℝ) (hb : 0 ≤ bound) (hp : 0 ≤ primaryError) (_ha : 0 ≤ anchorError)
    (hscore : ∀ color, |score color| ≤ bound)
    (hprimary : ∀ color, |approximatePrimary.weight color-primary.weight color| ≤ primaryError)
    (hanchor : ∀ color output, |(approximateAnchor color).weight output-(anchor color).weight output| ≤ anchorError)
    (output : Body) :
    |ControlCoordinates.anchorProfile approximatePrimary approximateAnchor score output-
      ControlCoordinates.anchorProfile primary anchor score output| ≤
      (Fintype.card Primary:ℝ)*bound*(primaryError+anchorError) := by
  unfold ControlCoordinates.anchorProfile
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _color : Primary, bound*(primaryError+anchorError) := by
      apply Finset.sum_le_sum
      intro color _
      calc
        _ = |score color*((approximatePrimary.weight color-primary.weight color)*(approximateAnchor color).weight output +
            primary.weight color*((approximateAnchor color).weight output-(anchor color).weight output))| := by congr 1; ring
        _ ≤ |score color| * (|approximatePrimary.weight color-primary.weight color| * (approximateAnchor color).weight output +
            primary.weight color*|(approximateAnchor color).weight output-(anchor color).weight output|) := by
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          simpa only [abs_mul, abs_of_nonneg ((approximateAnchor color).nonneg output),
            abs_of_nonneg (primary.nonneg color)] using abs_add_le
              ((approximatePrimary.weight color-primary.weight color)*(approximateAnchor color).weight output)
              (primary.weight color*((approximateAnchor color).weight output-(anchor color).weight output))
        _ ≤ bound*(primaryError*1+1*anchorError) := by
          apply mul_le_mul (hscore color) _
            (add_nonneg (mul_nonneg (abs_nonneg _) ((approximateAnchor color).nonneg output))
              (mul_nonneg (primary.nonneg color) (abs_nonneg _))) hb
          exact add_le_add (mul_le_mul (hprimary color) ((approximateAnchor color).atom_le_one output)
            ((approximateAnchor color).nonneg output) hp)
            (mul_le_mul (primary.atom_le_one color) (hanchor color output) (abs_nonneg _) (by norm_num))
        _ = _ := by ring
    _ = _ := by simp [mul_assoc]
open _root_.P2M9e1cfc64 renaming h358 → _p2mH358
end Generic
open _root_.P2M9e1cfc64 renaming h357 → _p2mH357
open _root_.P2M9e1cfc64 renaming h358 → _p2mH358
end
open _root_.P2M9e1cfc64 renaming h357 → _p2mH357
open _root_.P2M9e1cfc64 renaming h358 → _p2mH358
end CurrentAFT.RationalPairedLiftProgram
open _root_.P2M9e1cfc64 renaming h357 → _p2mH357
open _root_.P2M9e1cfc64 renaming h358 → _p2mH358
end
open _root_.P2M9e1cfc64 renaming h357 → _p2mH357
open _root_.P2M9e1cfc64 renaming h358 → _p2mH358
section
namespace CurrentAFT.RationalRootMassProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary
  RationalProposalProgram LocalReferenceEnergy
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base primaryLaw centerLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h417 (security cutoff bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : ℕ → ℚ) (word : Fin 4 → ℕ) :
    scalarAverage security cutoff bits compensatorRoot attachmentRoot score word =
      ∑ scalar : Window cutoff, gaussianWeight security cutoff bits scalar *
        fixedMass security bits compensatorRoot attachmentRoot scalar.val score word := by
  unfold scalarAverage
  exact (FiniteConvolutionProgram.windowIndexEquiv cutoff).sum_comp
    (fun scalar : Window cutoff => gaussianWeight security cutoff bits scalar *
      fixedMass security bits compensatorRoot attachmentRoot scalar.val score word)
open _root_.P2M9e1cfc64 renaming h417 → _p2mH417
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h408 (security : ℕ) (score : FirstHistogram.Palette security → ℝ)
    (primaryColor centerColor : FirstHistogram.Palette security) :
    actualWeightedScore security score primaryColor centerColor =
      (centerLaw security).weight centerColor * PairedResponse.pairedScore security score primaryColor centerColor := by
  unfold actualWeightedScore PairedResponse.pairedScore PairedResponse.compensatorScore
  by_cases hzero : (centerLaw security).weight centerColor = 0
  · rw [hzero, PairedResponse.centerLaw_zero_implies_anchorScore_zero security score centerColor hzero]
    ring
  · field_simp
open _root_.P2M9e1cfc64 renaming h408 → _p2mH408
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h409 (security bits : ℕ) (score : ℕ → ℚ) (output : FirstHistogram.Palette security) :
    (anchorScore security bits score output.val : ℝ) =
      ControlCoordinates.anchorProfile (approximatePrimaryLaw security bits) (approximateAnchorLaw security bits)
        (fun color : FirstHistogram.Palette security => (score color.val : ℝ)) output := by
  unfold anchorScore
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, anchor_cast, ControlCoordinates.anchorProfile]
  apply Finset.sum_congr rfl
  intro color _
  change (approximateAnchorLaw security bits color).weight output *
    (approximatePrimaryLaw security bits).weight color * (score color.val : ℝ) = _
  ring
open _root_.P2M9e1cfc64 renaming h409 → _p2mH409
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h405 (security : ℕ) (score : FirstHistogram.Palette security → ℝ)
    (output : FirstHistogram.Palette security) :
    PairedResponse.anchorWeightedScore security score output =
      ControlCoordinates.anchorProfile (primaryLaw security) (InwardAnchor.smoothedAnchorLaw security) score output := by
  unfold PairedResponse.anchorWeightedScore ControlCoordinates.anchorProfile
  apply Finset.sum_congr rfl
  intro color _
  ring
open _root_.P2M9e1cfc64 renaming h405 → _p2mH405
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h419 (security bits : ℕ) (score : ℕ → ℚ)
    (primaryColor centerColor : FirstHistogram.Palette security) :
    (weightedScore security bits score primaryColor.val centerColor.val : ℝ) =
      (approximateCenterLaw security bits).weight centerColor * (score primaryColor.val : ℝ) -
        (LocalPairProgram.activationApprox security bits : ℝ) *
          ControlCoordinates.anchorProfile (approximatePrimaryLaw security bits) (approximateAnchorLaw security bits)
            (fun color : FirstHistogram.Palette security => (score color.val : ℝ)) centerColor := by
  simp only [weightedScore, Rat.cast_sub, Rat.cast_mul, _p2mH409]
  rfl
open _root_.P2M9e1cfc64 renaming h419 → _p2mH419
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h418 (security bits : ℕ) (score : ℕ → ℚ) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color : FirstHistogram.Palette security, |(score color.val : ℝ)| ≤ bound)
    (primaryColor centerColor : FirstHistogram.Palette security) :
    |(weightedScore security bits score primaryColor.val centerColor.val : ℝ)| ≤ 2 * bound := by
  rw [_p2mH419]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg ((approximateCenterLaw security bits).nonneg centerColor),
    abs_mul, abs_of_nonneg (LocalPairProgram.activationApprox_bounds security bits).1]
  have hp := _p2mH357 (approximatePrimaryLaw security bits)
    (approximateAnchorLaw security bits) (fun color : FirstHistogram.Palette security => (score color.val : ℝ))
    bound hscore centerColor
  have hc := (approximateCenterLaw security bits).atom_le_one centerColor
  have ha := (LocalPairProgram.activationApprox_bounds security bits).2
  have hfirst := mul_le_mul hc (hscore primaryColor) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hsecond := mul_le_mul ha hp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith
open _root_.P2M9e1cfc64 renaming h418 → _p2mH418
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h404 (security : ℕ) (score : FirstHistogram.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hscore : ∀ color, |score color| ≤ bound)
    (primaryColor centerColor : FirstHistogram.Palette security) :
    |actualWeightedScore security score primaryColor centerColor| ≤ 2 * bound := by
  rw [actualWeightedScore, _p2mH405]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg ((centerLaw security).nonneg centerColor),
    abs_mul, abs_of_pos (activation_pos security)]
  have hp := _p2mH357 (primaryLaw security)
    (InwardAnchor.smoothedAnchorLaw security) score bound hscore centerColor
  have hfirst := mul_le_mul ((centerLaw security).atom_le_one centerColor) (hscore primaryColor)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hsecond := mul_le_mul (activation_le_half security) hp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith
open _root_.P2M9e1cfc64 renaming h404 → _p2mH404
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h420 (security bits : ℕ) (score : ℕ → ℚ) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color : FirstHistogram.Palette security, |(score color.val : ℝ)| ≤ bound)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (primaryColor centerColor : FirstHistogram.Palette security) :
    |(weightedScore security bits score primaryColor.val centerColor.val : ℝ) -
      actualWeightedScore security (fun color => (score color.val : ℝ)) primaryColor centerColor| ≤
        weightedErrorConstant security * bound * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let C := primaryErrorConstant security
  have he : 0 ≤ epsilon := by positivity
  have hC : 0 ≤ C := by dsimp [C, primaryErrorConstant]; positivity
  have hp (color : FirstHistogram.Palette security) :
      |(approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color| ≤ C * epsilon := by
    simpa only [approximatePrimaryLaw, primaryLaw, C, primaryErrorConstant, epsilon] using
      _p2mH392 security bits color hprecision hbudget
  have hc : |(approximateCenterLaw security bits).weight centerColor - (centerLaw security).weight centerColor| ≤
      (C * Parameters.modulus security + 2) * epsilon := by
    simpa only [approximateCenterLaw, centerLaw, C, primaryErrorConstant, epsilon] using
      _p2mH384 security bits centerColor hprecision hbudget
  have hanchor := _p2mH358 (primaryLaw security) (approximatePrimaryLaw security bits)
    (InwardAnchor.smoothedAnchorLaw security) (approximateAnchorLaw security bits)
    (fun color : FirstHistogram.Palette security => (score color.val : ℝ)) bound (C * epsilon) epsilon hb
    (mul_nonneg hC he) he hscore hp (fun color output => by
      simpa only [← anchor_cast] using _p2mH381 security bits color output) centerColor
  have ha := _p2mH130 security bits
  have hprofile := _p2mH357 (approximatePrimaryLaw security bits)
    (approximateAnchorLaw security bits) (fun color : FirstHistogram.Palette security => (score color.val : ℝ))
    bound hscore centerColor
  rw [_p2mH419, actualWeightedScore, _p2mH405]
  let approxProfile := ControlCoordinates.anchorProfile (approximatePrimaryLaw security bits) (approximateAnchorLaw security bits)
    (fun color : FirstHistogram.Palette security => (score color.val : ℝ)) centerColor
  let profile := ControlCoordinates.anchorProfile (primaryLaw security) (InwardAnchor.smoothedAnchorLaw security)
    (fun color : FirstHistogram.Palette security => (score color.val : ℝ)) centerColor
  calc
    _ = |((approximateCenterLaw security bits).weight centerColor - (centerLaw security).weight centerColor) *
          (score primaryColor.val : ℝ) -
        (((LocalPairProgram.activationApprox security bits : ℝ) - DiffuseProfiles.activation security) * approxProfile +
          DiffuseProfiles.activation security * (approxProfile - profile))| := by dsimp only [approxProfile, profile]; congr 1; ring
    _ ≤ |((approximateCenterLaw security bits).weight centerColor - (centerLaw security).weight centerColor) *
          (score primaryColor.val : ℝ)| +
        |((LocalPairProgram.activationApprox security bits : ℝ) - DiffuseProfiles.activation security) * approxProfile| +
          |DiffuseProfiles.activation security * (approxProfile - profile)| := by
      have hsplit := abs_sub
        (((approximateCenterLaw security bits).weight centerColor - (centerLaw security).weight centerColor) *
          (score primaryColor.val : ℝ))
        (((LocalPairProgram.activationApprox security bits : ℝ) - DiffuseProfiles.activation security) * approxProfile +
          DiffuseProfiles.activation security * (approxProfile - profile))
      have hsum := abs_add_le
        (((LocalPairProgram.activationApprox security bits : ℝ) - DiffuseProfiles.activation security) * approxProfile)
        (DiffuseProfiles.activation security * (approxProfile - profile))
      linarith
    _ ≤ ((C * Parameters.modulus security + 2) * epsilon) * bound +
        ((1 / 2 : ℝ) * epsilon) * bound +
        (1 / 2 : ℝ) * ((Parameters.modulus security : ℝ) * bound * (C * epsilon + epsilon)) := by
      simp only [abs_mul]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul hc (hscore primaryColor) (abs_nonneg _) (by positivity)
        · exact mul_le_mul ha hprofile (abs_nonneg _) (by positivity)
      · rw [abs_of_pos (activation_pos security)]
        exact mul_le_mul (activation_le_half security) (by simpa only [Fintype.card_fin] using hanchor)
          (abs_nonneg _) (by norm_num)
    _ ≤ _ := by
      change _ ≤ ((C * Parameters.modulus security + 2) + 1 +
        (Parameters.modulus security : ℝ) * (C + 1)) * bound * epsilon
      have hq : 0 ≤ (Parameters.modulus security : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hq hb) he,
        mul_nonneg (mul_nonneg (mul_nonneg hq hb) hC) he]
open _root_.P2M9e1cfc64 renaming h420 → _p2mH420
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h410 (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (centerColor : FirstHistogram.Palette security)
    (word : Fin 4 → FirstHistogram.Palette security) :
    (controlRest security compensatorRoot attachmentRoot scalar.val centerColor.val
      (fun index => (word index).val) : ℝ) =
        actualRest security compensatorRoot attachmentRoot scalar centerColor word := by
  have hmargin : 3 * (security + 2)^2 = Parameters.safeMargin security := by
    simp only [Parameters.safeMargin, Parameters.sourceCutoff, Parameters.base]
  unfold controlRest
  rw [PublicParameterProgram.modulus_value, hmargin]
  simp only [Rat.cast_mul]
  rw [bodyKernel_cast]
  change (attachmentAt security attachmentRoot scalar).weight (word 3) * _ = _
  unfold actualRest FirstHistogram.atom
  by_cases hshift : shiftEquiv security compensatorRoot centerColor = word 0
  · simp only [if_pos ((shift_condition security _ _ _).mp hshift), if_pos hshift, Rat.cast_one]
  · simp only [if_neg (mt (shift_condition security _ _ _).mpr hshift), if_neg hshift, Rat.cast_zero]
open _root_.P2M9e1cfc64 renaming h410 → _p2mH410
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h403 (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (centerColor : FirstHistogram.Palette security)
    (word : Fin 4 → FirstHistogram.Palette security) :
    |actualRest security compensatorRoot attachmentRoot scalar centerColor word| ≤ 1 := by
  unfold actualRest FirstHistogram.atom
  split_ifs
  · rw [mul_one, abs_of_nonneg ((attachmentAt security attachmentRoot scalar).nonneg _)]
    exact (attachmentAt security attachmentRoot scalar).atom_le_one _
  · norm_num
open _root_.P2M9e1cfc64 renaming h403 → _p2mH403
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h411 (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : ℕ → ℚ)
    (word : Fin 4 → FirstHistogram.Palette security) :
    (fixedMass security bits compensatorRoot attachmentRoot scalar.val score (fun index => (word index).val) : ℝ) =
      ∑ primaryColor : FirstHistogram.Palette security, ∑ centerColor : FirstHistogram.Palette security,
        (approximatePrimaryLaw security bits).weight primaryColor *
          (weightedScore security bits score primaryColor.val centerColor.val : ℝ) *
            (LocalPairProgram.current security bits primaryColor.val scalar.val (word 1).val (word 2).val : ℝ) *
              actualRest security compensatorRoot attachmentRoot scalar centerColor word := by
  unfold fixedMass
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, _p2mH410]
  rfl
open _root_.P2M9e1cfc64 renaming h411 → _p2mH411
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h407 (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : FirstHistogram.Palette security → ℝ)
    (word : Fin 4 → FirstHistogram.Palette security) :
    PairedReferenceEnergy.pairedMassAt security compensatorRoot attachmentRoot scalar score word =
      ∑ primaryColor, ∑ centerColor, (primaryLaw security).weight primaryColor *
        actualWeightedScore security score primaryColor centerColor *
          (pairAt security primaryColor scalar).weight (word 1, word 2) *
            actualRest security compensatorRoot attachmentRoot scalar centerColor word := by
  rw [PairedReferenceEnergy.pairedMassAt_control_sum]
  apply Finset.sum_congr rfl
  intro primaryColor _
  apply Finset.sum_congr rfl
  intro centerColor _
  rw [_p2mH408]
  unfold actualRest FirstHistogram.atom
  split_ifs <;> ring
open _root_.P2M9e1cfc64 renaming h407 → _p2mH407
set_option maxRecDepth 8192
private theorem _root_.P2M9e1cfc64.h560 (a a' b b' c c' A B epsilon bound : ℝ)
    (ha : |a| ≤ 1) (ha' : |a' - a| ≤ A * epsilon)
    (hb : |b| ≤ 2 * bound) (hb' : |b'| ≤ 2 * bound)
    (hbdiff : |b' - b| ≤ B * bound * epsilon)
    (hc' : |c'| ≤ 4) (hcdiff : |c' - c| ≤ 3 * epsilon)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ epsilon) (hbound : 0 ≤ bound) :
    |a' * b' * c' - a * b * c| ≤ (8 * A + 4 * B + 6) * bound * epsilon := by
  calc
    _ = |(a' - a) * b' * c' + a * (b' - b) * c' + a * b * (c' - c)| := by congr 1; ring
    _ ≤ |(a' - a) * b' * c'| + |a * (b' - b) * c'| + |a * b * (c' - c)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (A * epsilon) * (2 * bound) * 4 + 1 * (B * bound * epsilon) * 4 +
        1 * (2 * bound) * (3 * epsilon) := by
      simp only [abs_mul]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul (mul_le_mul ha' hb' (abs_nonneg _) (by positivity)) hc'
            (abs_nonneg _) (by positivity)
        · exact mul_le_mul (mul_le_mul ha hbdiff (abs_nonneg _) (by norm_num)) hc'
            (abs_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul ha hb (abs_nonneg _) (by norm_num)) hcdiff
          (abs_nonneg _) (by positivity)
    _ = _ := by ring
open _root_.P2M9e1cfc64 renaming h560 → _p2mH560
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h412 (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : ℕ → ℚ) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color : FirstHistogram.Palette security, |(score color.val : ℝ)| ≤ bound)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (word : Fin 4 → FirstHistogram.Palette security) :
    |(fixedMass security bits compensatorRoot attachmentRoot scalar.val score (fun index => (word index).val) : ℝ) -
      PairedReferenceEnergy.pairedMassAt security compensatorRoot attachmentRoot scalar
        (fun color => (score color.val : ℝ)) word| ≤
          fixedErrorConstant security * bound * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let A := primaryErrorConstant security
  let B := weightedErrorConstant security
  have he : 0 ≤ epsilon := by positivity
  have he1 : epsilon ≤ 1 := by
    have ht : (1 : ℝ) ≤ (2 : ℝ)^bits := one_le_pow₀ (by norm_num)
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2^bits)).mpr (by simpa using ht)
  have hA : 0 ≤ A := by dsimp [A, primaryErrorConstant]; positivity
  have hB : 0 ≤ B := by dsimp [B, weightedErrorConstant, primaryErrorConstant]; positivity
  rw [_p2mH411, _p2mH407, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _primaryColor : FirstHistogram.Palette security,
        ∑ _centerColor : FirstHistogram.Palette security, (8 * A + 4 * B + 6) * bound * epsilon := by
      apply Finset.sum_le_sum
      intro primaryColor _
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro centerColor _
      let c' : ℝ := LocalPairProgram.current security bits primaryColor.val scalar.val (word 1).val (word 2).val
      let c := (pairAt security primaryColor scalar).weight (word 1, word 2)
      have hc : |c' - c| ≤ 3 * epsilon :=
        (_p2mH131 security bits primaryColor (word 1) (word 2) scalar).trans_eq (by dsimp [epsilon]; ring)
      have hc' : |c'| ≤ 4 := by
        have hctrue : |c| ≤ 1 := by
          rw [abs_of_nonneg ((pairAt security primaryColor scalar).nonneg _)]
          exact (pairAt security primaryColor scalar).atom_le_one _
        have h := (abs_add_le (c' - c) c).trans (add_le_add hc hctrue)
        have hsplit : c' - c + c = c' := by ring
        rw [hsplit] at h
        linarith
      have hp : |(approximatePrimaryLaw security bits).weight primaryColor - (primaryLaw security).weight primaryColor| ≤ A * epsilon := by
        simpa only [approximatePrimaryLaw, primaryLaw, A, primaryErrorConstant, epsilon] using
          _p2mH392 security bits primaryColor hprecision hbudget
      have hterm := _p2mH560 ((primaryLaw security).weight primaryColor)
        ((approximatePrimaryLaw security bits).weight primaryColor)
        (actualWeightedScore security (fun color => (score color.val : ℝ)) primaryColor centerColor)
        (weightedScore security bits score primaryColor.val centerColor.val : ℝ) c c' A B epsilon bound
        (by rw [abs_of_nonneg ((primaryLaw security).nonneg _)]; exact (primaryLaw security).atom_le_one _)
        hp (_p2mH404 security _ bound hb hscore _ _) (_p2mH418 security bits score bound hb hscore _ _)
        (_p2mH420 security bits score bound hb hscore hprecision hbudget _ _) hc' hc hA hB he hb
      rw [← sub_mul, abs_mul]
      exact (mul_le_mul hterm (_p2mH403 security compensatorRoot attachmentRoot scalar centerColor word)
        (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul];
                dsimp [fixedErrorConstant, A, B, epsilon]; ring
open _root_.P2M9e1cfc64 renaming h412 → _p2mH412
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h406 (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : FirstHistogram.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hscore : ∀ color, |score color| ≤ bound)
    (word : Fin 4 → FirstHistogram.Palette security) :
    |PairedReferenceEnergy.pairedMassAt security compensatorRoot attachmentRoot scalar score word| ≤
      (2 * (Parameters.modulus security : ℝ)^2) * bound := by
  rw [_p2mH407]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _primaryColor : FirstHistogram.Palette security,
        ∑ _centerColor : FirstHistogram.Palette security, 2 * bound := by
      apply Finset.sum_le_sum
      intro primaryColor _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro centerColor _
      simp only [abs_mul, abs_of_nonneg ((primaryLaw security).nonneg _),
        abs_of_nonneg ((pairAt security primaryColor scalar).nonneg _)]
      have h := mul_le_mul
        (mul_le_mul (mul_le_mul ((primaryLaw security).atom_le_one primaryColor)
          (_p2mH404 security score bound hb hscore primaryColor centerColor)
          (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
          ((pairAt security primaryColor scalar).atom_le_one (word 1, word 2))
          ((pairAt security primaryColor scalar).nonneg (word 1, word 2))
          (by positivity : (0 : ℝ) ≤ 1 * (2 * bound)))
        (_p2mH403 security compensatorRoot attachmentRoot scalar centerColor word)
        (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1 * (2 * bound) * 1)
      simpa only [one_mul, mul_one] using h
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
open _root_.P2M9e1cfc64 renaming h406 → _p2mH406
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h415 (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : ℕ → ℚ) (word : Fin 4 → FirstHistogram.Palette security) :
    (primaryMass security bits compensatorRoot attachmentRoot score (fun index => (word index).val) : ℝ) =
      ∑ scalar : FirstHistogram.Scalar security,
        (windowApproxLaw (WindowGaussianSampler.squaredWidth security)
          (Parameters.sourceCutoff security - 1) bits).weight scalar *
          (fixedMass security bits compensatorRoot attachmentRoot scalar.val score
            (fun index => (word index).val) : ℝ) := by
  have hcutoff : (security + 2)^2 - 1 = Parameters.sourceCutoff security - 1 := by
    simp only [Parameters.sourceCutoff, Parameters.base]
  unfold primaryMass
  rw [hcutoff]
  simp only [_p2mH417, Rat.cast_sum, Rat.cast_mul, gaussianWeight_eq]
  rfl
open _root_.P2M9e1cfc64 renaming h415 → _p2mH415
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h413 (security : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : FirstHistogram.Palette security → ℝ) (word : Fin 4 → FirstHistogram.Palette security) :
    RootMassColumns.primaryMassAt security roots score word =
      ∑ scalar : FirstHistogram.Scalar security, (scalarLaw security).weight scalar *
        PairedReferenceEnergy.pairedMassAt security roots.1.val roots.2.val scalar score word := by
  simp only [RootMassColumns.primaryMassAt, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PairedReferenceEnergy.pairedMassLinear_apply]
open _root_.P2M9e1cfc64 renaming h413 → _p2mH413
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h414 (security : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : FirstHistogram.Palette security → ℝ) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color, |score color| ≤ bound) (word : Fin 4 → FirstHistogram.Palette security) :
    |RootMassColumns.primaryMassAt security roots score word| ≤
      (2 * (Parameters.modulus security : ℝ)^2) * bound := by
  rw [_p2mH413]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ scalar, (scalarLaw security).weight scalar * ((2 * (Parameters.modulus security : ℝ)^2) * bound) := by
      apply Finset.sum_le_sum
      intro scalar _
      rw [abs_mul, abs_of_nonneg ((scalarLaw security).nonneg scalar)]
      exact mul_le_mul_of_nonneg_left (_p2mH406 security _ _ scalar score bound hb hscore word)
        ((scalarLaw security).nonneg scalar)
    _ = _ := by rw [← Finset.sum_mul, (scalarLaw security).sum_one, one_mul]
open _root_.P2M9e1cfc64 renaming h414 → _p2mH414
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h416 (security bits : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : ℕ → ℚ) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color : FirstHistogram.Palette security, |(score color.val : ℝ)| ≤ bound)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (word : Fin 4 → FirstHistogram.Palette security) :
    |(primaryMass security bits roots.1.val roots.2.val score (fun index => (word index).val) : ℝ) -
      RootMassColumns.primaryMassAt security roots (fun color => (score color.val : ℝ)) word| ≤
        primaryMassErrorConstant security * bound * (1 / (2 : ℝ)^bits) := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security)
    (Parameters.sourceCutoff security - 1) bits
  let test := fun scalar : FirstHistogram.Scalar security =>
    PairedReferenceEnergy.pairedMassAt security roots.1.val roots.2.val scalar
      (fun color => (score color.val : ℝ)) word
  let approximateTest := fun scalar : FirstHistogram.Scalar security =>
    (fixedMass security bits roots.1.val roots.2.val scalar.val score (fun index => (word index).val) : ℝ)
  have htest (scalar : FirstHistogram.Scalar security) :
      |test scalar| ≤ (2 * (Parameters.modulus security : ℝ)^2) * bound :=
    _p2mH406 security _ _ scalar _ bound hb hscore word
  have hl1 : (∑ scalar, |approximate.weight scalar - (scalarLaw security).weight scalar|) ≤ 1 / (2 : ℝ)^bits :=
    _p2mH14 _ _ _ _ (_p2mH549 security)
      (_p2mH550 security).symm
  have hsource : |approximate.expectation test - (scalarLaw security).expectation test| ≤
      (1 / (2 : ℝ)^bits) * ((2 * (Parameters.modulus security : ℝ)^2) * bound) := by
    unfold FiniteDist.expectation
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ scalar, |approximate.weight scalar - (scalarLaw security).weight scalar| *
          ((2 * (Parameters.modulus security : ℝ)^2) * bound) := by
        apply Finset.sum_le_sum
        intro scalar _
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (htest scalar) (abs_nonneg _)
      _ = _ := Finset.sum_mul .. |>.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hl1 (by positivity)
  have hentries : |approximate.expectation approximateTest - approximate.expectation test| ≤
      fixedErrorConstant security * bound * (1 / (2 : ℝ)^bits) := by
    unfold FiniteDist.expectation
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ scalar, approximate.weight scalar *
          (fixedErrorConstant security * bound * (1 / (2 : ℝ)^bits)) := by
        apply Finset.sum_le_sum
        intro scalar _
        rw [← mul_sub, abs_mul, abs_of_nonneg (approximate.nonneg scalar)]
        exact mul_le_mul_of_nonneg_left
          (_p2mH412 security bits _ _ scalar score bound hb hscore hprecision hbudget word)
          (approximate.nonneg scalar)
      _ = _ := by rw [← Finset.sum_mul, approximate.sum_one, one_mul]
  rw [_p2mH415, _p2mH413]
  change |approximate.expectation approximateTest - (scalarLaw security).expectation test| ≤ _
  calc
    _ ≤ |approximate.expectation approximateTest - approximate.expectation test| +
        |approximate.expectation test - (scalarLaw security).expectation test| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hentries hsource
    _ = _ := by unfold primaryMassErrorConstant; ring
open _root_.P2M9e1cfc64 renaming h416 → _p2mH416
end
open _root_.P2M9e1cfc64 renaming h403 → _p2mH403
open _root_.P2M9e1cfc64 renaming h404 → _p2mH404
open _root_.P2M9e1cfc64 renaming h405 → _p2mH405
open _root_.P2M9e1cfc64 renaming h406 → _p2mH406
open _root_.P2M9e1cfc64 renaming h407 → _p2mH407
open _root_.P2M9e1cfc64 renaming h408 → _p2mH408
open _root_.P2M9e1cfc64 renaming h409 → _p2mH409
open _root_.P2M9e1cfc64 renaming h410 → _p2mH410
open _root_.P2M9e1cfc64 renaming h411 → _p2mH411
open _root_.P2M9e1cfc64 renaming h412 → _p2mH412
open _root_.P2M9e1cfc64 renaming h413 → _p2mH413
open _root_.P2M9e1cfc64 renaming h414 → _p2mH414
open _root_.P2M9e1cfc64 renaming h415 → _p2mH415
open _root_.P2M9e1cfc64 renaming h416 → _p2mH416
open _root_.P2M9e1cfc64 renaming h417 → _p2mH417
open _root_.P2M9e1cfc64 renaming h418 → _p2mH418
open _root_.P2M9e1cfc64 renaming h419 → _p2mH419
open _root_.P2M9e1cfc64 renaming h420 → _p2mH420
open _root_.P2M9e1cfc64 renaming h560 → _p2mH560
end CurrentAFT.RationalRootMassProgram
open _root_.P2M9e1cfc64 renaming h403 → _p2mH403
open _root_.P2M9e1cfc64 renaming h404 → _p2mH404
open _root_.P2M9e1cfc64 renaming h405 → _p2mH405
open _root_.P2M9e1cfc64 renaming h406 → _p2mH406
open _root_.P2M9e1cfc64 renaming h407 → _p2mH407
open _root_.P2M9e1cfc64 renaming h408 → _p2mH408
open _root_.P2M9e1cfc64 renaming h409 → _p2mH409
open _root_.P2M9e1cfc64 renaming h410 → _p2mH410
open _root_.P2M9e1cfc64 renaming h411 → _p2mH411
open _root_.P2M9e1cfc64 renaming h412 → _p2mH412
open _root_.P2M9e1cfc64 renaming h413 → _p2mH413
open _root_.P2M9e1cfc64 renaming h414 → _p2mH414
open _root_.P2M9e1cfc64 renaming h415 → _p2mH415
open _root_.P2M9e1cfc64 renaming h416 → _p2mH416
open _root_.P2M9e1cfc64 renaming h417 → _p2mH417
open _root_.P2M9e1cfc64 renaming h418 → _p2mH418
open _root_.P2M9e1cfc64 renaming h419 → _p2mH419
open _root_.P2M9e1cfc64 renaming h420 → _p2mH420
open _root_.P2M9e1cfc64 renaming h560 → _p2mH560
end
open _root_.P2M9e1cfc64 renaming h410 → _p2mH410
open _root_.P2M9e1cfc64 renaming h414 → _p2mH414
open _root_.P2M9e1cfc64 renaming h408 → _p2mH408
open _root_.P2M9e1cfc64 renaming h413 → _p2mH413
open _root_.P2M9e1cfc64 renaming h409 → _p2mH409
open _root_.P2M9e1cfc64 renaming h419 → _p2mH419
open _root_.P2M9e1cfc64 renaming h406 → _p2mH406
open _root_.P2M9e1cfc64 renaming h415 → _p2mH415
open _root_.P2M9e1cfc64 renaming h405 → _p2mH405
open _root_.P2M9e1cfc64 renaming h412 → _p2mH412
open _root_.P2M9e1cfc64 renaming h404 → _p2mH404
open _root_.P2M9e1cfc64 renaming h417 → _p2mH417
open _root_.P2M9e1cfc64 renaming h418 → _p2mH418
open _root_.P2M9e1cfc64 renaming h403 → _p2mH403
open _root_.P2M9e1cfc64 renaming h420 → _p2mH420
open _root_.P2M9e1cfc64 renaming h416 → _p2mH416
open _root_.P2M9e1cfc64 renaming h411 → _p2mH411
open _root_.P2M9e1cfc64 renaming h407 → _p2mH407
section
namespace CurrentAFT.RationalPositiveReferenceProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary
  RationalProposalProgram LocalReferenceEnergy RationalRootMassProgram
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalPositiveReferenceProgram.classicalFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h367 (security bits : ℕ) (word : Fin 4 → ℕ) :
    current security bits word =
      ∑ scalar : Window (Parameters.sourceCutoff security-1),
        gaussianWeight security (Parameters.sourceCutoff security-1) bits scalar*
          seedEvaluate security bits (fun compensator => seedEvaluate security bits (fun attachment =>
            fixedMass security bits (actualBlur security compensator) (actualBlur security attachment) scalar.val word)) := by
  unfold current
  exact (AFT.FiniteConvolutionProgram.windowIndexEquiv (Parameters.sourceCutoff security-1)).sum_comp
    (fun scalar => gaussianWeight security (Parameters.sourceCutoff security-1) bits scalar*
      seedEvaluate security bits (fun compensator => seedEvaluate security bits (fun attachment =>
        fixedMass security bits (actualBlur security compensator) (actualBlur security attachment) scalar.val word)))
open _root_.P2M9e1cfc64 renaming h367 → _p2mH367
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h369 (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (word : Fin 4 → FirstHistogram.Palette security) :
    (fixedMass security bits compensatorRoot attachmentRoot scalar.val (fun i => (word i).val) : ℝ) =
      ∑ primaryColor : FirstHistogram.Palette security, ∑ centerColor : FirstHistogram.Palette security,
        (approximatePrimaryLaw security bits).weight primaryColor *
          (approximateCenterLaw security bits).weight centerColor *
            (LocalPairProgram.current security bits primaryColor.val scalar.val (word 1).val (word 2).val : ℝ) *
              actualRest security compensatorRoot attachmentRoot scalar centerColor word := by
  unfold fixedMass
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, _p2mH410]
  rfl
open _root_.P2M9e1cfc64 renaming h369 → _p2mH369
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h365 (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (word : Fin 4 → FirstHistogram.Palette security) :
    (PositiveFirstCoefficient.positiveFourLaw security compensatorRoot attachmentRoot scalar).weight word =
      ∑ primaryColor, ∑ centerColor, (primaryLaw security).weight primaryColor *
        (centerLaw security).weight centerColor *
          (pairAt security primaryColor scalar).weight (word 1, word 2) *
            actualRest security compensatorRoot attachmentRoot scalar centerColor word := by
  rw [IndependentReferenceEnergy.fixedPositive_control]
  simp only [PhysicalSynthesis.groupLaw, FiniteDist.prod_weight, Fintype.sum_prod_type,
    FixedPairedFirst.fixedControlLaw_weight]
  apply Finset.sum_congr rfl
  intro primaryColor _
  apply Finset.sum_congr rfl
  intro centerColor _
  unfold actualRest PairedReferenceEnergy.controlMass FirstHistogram.atom
  split_ifs <;> ring
open _root_.P2M9e1cfc64 renaming h365 → _p2mH365
set_option maxRecDepth 8192
private theorem _root_.P2M9e1cfc64.h558 (a a' b b' c c' A B epsilon : ℝ)
    (ha : |a| ≤ 1) (hda : |a' - a| ≤ A * epsilon)
    (hb : |b| ≤ 1) (hb' : |b'| ≤ 1) (hdb : |b' - b| ≤ B * epsilon)
    (hc' : |c'| ≤ 4) (hdc : |c' - c| ≤ 3 * epsilon)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ epsilon) :
    |a' * b' * c' - a * b * c| ≤ (4 * A + 4 * B + 3) * epsilon := by
  calc
    _ = |(a'-a)*b'*c' + a*(b'-b)*c' + a*b*(c'-c)| := by congr 1; ring
    _ ≤ |(a'-a)*b'*c'| + |a*(b'-b)*c'| + |a*b*(c'-c)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (A*epsilon)*1*4 + 1*(B*epsilon)*4 + 1*1*(3*epsilon) := by
      simp only [abs_mul]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul (mul_le_mul hda hb' (abs_nonneg _) (by positivity)) hc'
            (abs_nonneg _) (by positivity)
        · exact mul_le_mul (mul_le_mul ha hdb (abs_nonneg _) (by norm_num)) hc'
            (abs_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul ha hb (abs_nonneg _) (by norm_num)) hdc
          (abs_nonneg _) (by norm_num)
    _ = _ := by ring
open _root_.P2M9e1cfc64 renaming h558 → _p2mH558
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h370 (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (word : Fin 4 → FirstHistogram.Palette security) :
    |(fixedMass security bits compensatorRoot attachmentRoot scalar.val (fun i => (word i).val) : ℝ) -
      (PositiveFirstCoefficient.positiveFourLaw security compensatorRoot attachmentRoot scalar).weight word| ≤
        fixedErrorConstant security * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let A := primaryErrorConstant security
  let B := A * Parameters.modulus security + 2
  have he : 0 ≤ epsilon := by positivity
  have he1 : epsilon ≤ 1 := by
    have hpow : (1 : ℝ) ≤ 2^bits := one_le_pow₀ (by norm_num)
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2^bits)).mpr (by simpa using hpow)
  have hA : 0 ≤ A := by dsimp [A, primaryErrorConstant]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  rw [_p2mH369, _p2mH365, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _primaryColor : FirstHistogram.Palette security,
        ∑ _centerColor : FirstHistogram.Palette security, (4*A+4*B+3)*epsilon := by
      apply Finset.sum_le_sum
      intro primaryColor _
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro centerColor _
      let c' : ℝ := LocalPairProgram.current security bits primaryColor.val scalar.val (word 1).val (word 2).val
      let c := (pairAt security primaryColor scalar).weight (word 1, word 2)
      have hc : |c'-c| ≤ 3*epsilon :=
        (_p2mH131 security bits primaryColor (word 1) (word 2) scalar).trans_eq (by dsimp [epsilon]; ring)
      have hctrue : |c| ≤ 1 := by
        rw [abs_of_nonneg ((pairAt security primaryColor scalar).nonneg _)]
        exact (pairAt security primaryColor scalar).atom_le_one _
      have hc' : |c'| ≤ 4 := by
        have h := (abs_add_le (c'-c) c).trans (add_le_add hc hctrue)
        have hid : c'-c+c=c' := by ring
        rw [hid] at h
        linarith
      have hp : |(approximatePrimaryLaw security bits).weight primaryColor - (primaryLaw security).weight primaryColor| ≤ A*epsilon := by
        simpa only [approximatePrimaryLaw, primaryLaw, A, primaryErrorConstant, epsilon] using
          _p2mH392 security bits primaryColor hprecision hbudget
      have hb : |(approximateCenterLaw security bits).weight centerColor - (centerLaw security).weight centerColor| ≤ B*epsilon := by
        simpa only [approximateCenterLaw, centerLaw, B, A, primaryErrorConstant, epsilon] using
          _p2mH384 security bits centerColor hprecision hbudget
      have hterm := _p2mH558 ((primaryLaw security).weight primaryColor)
        ((approximatePrimaryLaw security bits).weight primaryColor) ((centerLaw security).weight centerColor)
        ((approximateCenterLaw security bits).weight centerColor) c c' A B epsilon
        (by rw [abs_of_nonneg ((primaryLaw security).nonneg _)]; exact (primaryLaw security).atom_le_one _) hp
        (by rw [abs_of_nonneg ((centerLaw security).nonneg _)]; exact (centerLaw security).atom_le_one _)
        (by rw [abs_of_nonneg ((approximateCenterLaw security bits).nonneg _)]; exact (approximateCenterLaw security bits).atom_le_one _) hb
        hc' hc hA hB he
      rw [← sub_mul, abs_mul]
      exact (mul_le_mul hterm (_p2mH403 security compensatorRoot attachmentRoot scalar centerColor word)
        (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [fixedErrorConstant, A, B, epsilon]
      ring
open _root_.P2M9e1cfc64 renaming h370 → _p2mH370
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h366 (security bits : ℕ) (word : Fin 4 → FirstHistogram.Palette security) :
    (current security bits (fun i => (word i).val) : ℝ) =
      (approximateRootLaw security bits).expectation (fun roots =>
        (fixedMass security bits (actualBlur security roots.2.1) (actualBlur security roots.2.2)
          roots.1.val (fun i => (word i).val) : ℝ)) := by
  simp only [_p2mH367, Rat.cast_sum, Rat.cast_mul, gaussianWeight_eq, seedEvaluate_cast]
  unfold approximateRootLaw
  simp only [FiniteDist.expectation_prod]
  rfl
open _root_.P2M9e1cfc64 renaming h366 → _p2mH366
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h371 (security bits : ℕ) :
    (∑ roots, |(approximateRootLaw security bits).weight roots -
      (IndependentReferenceEnergy.rootLaw security).weight roots|) ≤ 7 * (1 / (2 : ℝ)^bits) := by
  have hs := _p2mH14 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security - 1) bits (_p2mH549 security)
    (_p2mH550 security).symm
  have hp := FiniteDist.l1_prod_le (approximateSeedLaw security bits) (actualSeedLaw security)
    (approximateSeedLaw security bits) (actualSeedLaw security)
  have hall := FiniteDist.l1_prod_le
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits)
    (scalarLaw security) ((approximateSeedLaw security bits).prod (approximateSeedLaw security bits))
    ((actualSeedLaw security).prod (actualSeedLaw security))
  exact hall.trans ((add_le_add hs (hp.trans (add_le_add (_p2mH393 security bits) (_p2mH393 security bits)))).trans_eq (by ring))
open _root_.P2M9e1cfc64 renaming h371 → _p2mH371
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h368 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (word : Fin 4 → FirstHistogram.Palette security) :
    |(current security bits (fun i => (word i).val) : ℝ) -
      (NormalizedLocalPolynomial.independentPositiveLaw security).weight word| ≤
        errorConstant security * (1 / (2 : ℝ)^bits) := by
  let approximate := approximateRootLaw security bits
  let actual := IndependentReferenceEnergy.rootLaw security
  let test := fun roots : IndependentReferenceEnergy.Roots security =>
    (PositiveFirstCoefficient.positiveFourLaw security (actualBlur security roots.2.1)
      (actualBlur security roots.2.2) roots.1).weight word
  let computed := fun roots : IndependentReferenceEnergy.Roots security =>
    (fixedMass security bits (actualBlur security roots.2.1) (actualBlur security roots.2.2)
      roots.1.val (fun i => (word i).val) : ℝ)
  have hsource : |approximate.expectation test - actual.expectation test| ≤ 7 * (1 / (2 : ℝ)^bits) := by
    have h := _p2mH70 approximate actual test 1
      (fun roots => by
        rw [abs_of_nonneg (FiniteDist.nonneg _ _)]
        exact FiniteDist.atom_le_one _ _)
    exact h.trans (by simpa only [one_mul] using _p2mH371 security bits)
  have hentries : |approximate.expectation computed - approximate.expectation test| ≤
      fixedErrorConstant security * (1 / (2 : ℝ)^bits) := by
    unfold FiniteDist.expectation
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ roots, approximate.weight roots * (fixedErrorConstant security * (1 / (2 : ℝ)^bits)) := by
        apply Finset.sum_le_sum
        intro roots _
        rw [← mul_sub, abs_mul, abs_of_nonneg (approximate.nonneg roots)]
        exact mul_le_mul_of_nonneg_left (_p2mH370 security bits _ _ roots.1 hprecision hbudget word)
          (approximate.nonneg roots)
      _ = _ := by rw [← Finset.sum_mul, approximate.sum_one, one_mul]
  rw [_p2mH366, IndependentReferenceEnergy.independentPositive_mixture]
  change |approximate.expectation computed - actual.expectation test| ≤ _
  exact ((abs_sub_le _ _ _).trans (add_le_add hentries hsource)).trans_eq (by unfold errorConstant; ring)
open _root_.P2M9e1cfc64 renaming h368 → _p2mH368
end
open _root_.P2M9e1cfc64 renaming h365 → _p2mH365
open _root_.P2M9e1cfc64 renaming h366 → _p2mH366
open _root_.P2M9e1cfc64 renaming h367 → _p2mH367
open _root_.P2M9e1cfc64 renaming h368 → _p2mH368
open _root_.P2M9e1cfc64 renaming h369 → _p2mH369
open _root_.P2M9e1cfc64 renaming h370 → _p2mH370
open _root_.P2M9e1cfc64 renaming h371 → _p2mH371
open _root_.P2M9e1cfc64 renaming h558 → _p2mH558
end CurrentAFT.RationalPositiveReferenceProgram
open _root_.P2M9e1cfc64 renaming h365 → _p2mH365
open _root_.P2M9e1cfc64 renaming h366 → _p2mH366
open _root_.P2M9e1cfc64 renaming h367 → _p2mH367
open _root_.P2M9e1cfc64 renaming h368 → _p2mH368
open _root_.P2M9e1cfc64 renaming h369 → _p2mH369
open _root_.P2M9e1cfc64 renaming h370 → _p2mH370
open _root_.P2M9e1cfc64 renaming h371 → _p2mH371
open _root_.P2M9e1cfc64 renaming h558 → _p2mH558
end
open _root_.P2M9e1cfc64 renaming h368 → _p2mH368
open _root_.P2M9e1cfc64 renaming h366 → _p2mH366
open _root_.P2M9e1cfc64 renaming h371 → _p2mH371
open _root_.P2M9e1cfc64 renaming h365 → _p2mH365
open _root_.P2M9e1cfc64 renaming h369 → _p2mH369
open _root_.P2M9e1cfc64 renaming h367 → _p2mH367
open _root_.P2M9e1cfc64 renaming h370 → _p2mH370
section
namespace CurrentAFT.RationalDensityInverseProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h177 (security : ℕ) (profile : FirstHistogram.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hprofile : ∀ color, |profile color| ≤ bound)
    (output : FirstHistogram.Palette security) :
    |(FirstResponse.responseEquiv security).symm profile output| ≤ inverseBound security*bound := by
  have hfunctional : |signFunctional (FirstResponse.anchorSign security) profile| ≤
      (Parameters.modulus security:ℝ)*bound := by
    apply (signFunctional_abs_le_l1 _ _ (FirstResponse.anchorSign_abs_le_one security)).trans
    calc
      _ ≤ ∑ _color : FirstHistogram.Palette security, bound := Finset.sum_le_sum (fun color _ => hprofile color)
      _ = _ := by simp
  have hlo := _p2mH215 security
  have hb0 := FirstResponse.base_pos security
  have hpos : 0 < RationalFirstResponseProgram.actualDenominator security :=
    (by positivity : (0:ℝ)<1/(16*(Parameters.base security:ℝ))).trans_le hlo
  have hinv : (RationalFirstResponseProgram.actualDenominator security)⁻¹ ≤ 16*(Parameters.base security:ℝ) := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le
      (by positivity : (0:ℝ)<1/(16*(Parameters.base security:ℝ))) hlo
  rw [_p2mH85]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ ≤ |profile output| +
        |(RationalFirstResponseProgram.actualDenominator security)⁻¹ *
          signFunctional (FirstResponse.anchorSign security) profile * DiffuseProfiles.signProfile security output| := abs_sub _ _
    _ = |profile output| + (RationalFirstResponseProgram.actualDenominator security)⁻¹ *
        |signFunctional (FirstResponse.anchorSign security) profile| * |DiffuseProfiles.signProfile security output| := by
      simp only [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
    _ ≤ bound+(16*(Parameters.base security:ℝ))*((Parameters.modulus security:ℝ)*bound)*2 :=
      add_le_add (hprofile output)
        (mul_le_mul (mul_le_mul hinv hfunctional (abs_nonneg _) (by positivity))
          (_p2mH217 security output) (abs_nonneg _) (by positivity))
    _ = _ := by unfold inverseBound; ring
open _root_.P2M9e1cfc64 renaming h177 → _p2mH177
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h179 (u v a b lower numeratorError denominatorError bound : ℝ)
    (hl : 0 < lower) (ha : lower ≤ a) (hb : lower ≤ b)
    (hen : 0 ≤ numeratorError) (hed : 0 ≤ denominatorError) (hbound : 0 ≤ bound)
    (hn : |u-v| ≤ numeratorError) (hd : |a-b| ≤ denominatorError) (hv : |v| ≤ bound) :
    |u/a-v/b| ≤ numeratorError/lower + bound*denominatorError/lower^2 := by
  have ha0 := hl.trans_le ha
  have hb0 := hl.trans_le hb
  have hai : a⁻¹ ≤ lower⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hl ha
  have hbi : b⁻¹ ≤ lower⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hl hb
  have hi : |a⁻¹-b⁻¹| ≤ denominatorError*lower⁻¹^2 := by
    calc
      _ = |(b-a)*(a⁻¹*b⁻¹)| := by congr 1; field_simp
      _ = |a-b| * (a⁻¹*b⁻¹) := by
        rw [abs_mul, abs_sub_comm b a, abs_of_pos (mul_pos (inv_pos.mpr ha0) (inv_pos.mpr hb0))]
      _ ≤ denominatorError*(lower⁻¹*lower⁻¹) :=
        mul_le_mul hd (mul_le_mul hai hbi (inv_nonneg.mpr hb0.le) (inv_nonneg.mpr hl.le))
          (mul_nonneg (inv_nonneg.mpr ha0.le) (inv_nonneg.mpr hb0.le)) hed
      _ = _ := by ring
  calc
    _ = |(u-v)*a⁻¹+v*(a⁻¹-b⁻¹)| := by congr 1; ring
    _ ≤ |(u-v)*a⁻¹|+|v*(a⁻¹-b⁻¹)| := abs_add_le _ _
    _ = |u-v| * a⁻¹+|v| * |a⁻¹-b⁻¹| := by rw [abs_mul, abs_of_pos (inv_pos.mpr ha0), abs_mul]
    _ ≤ numeratorError*lower⁻¹+bound*(denominatorError*lower⁻¹^2) :=
      add_le_add (mul_le_mul hn hai (inv_nonneg.mpr ha0.le) hen)
        (mul_le_mul hv hi (abs_nonneg _) hbound)
    _ = _ := by ring
open _root_.P2M9e1cfc64 renaming h179 → _p2mH179
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h176 (security bits : ℕ)
    (hprecision : RationalFirstResponseProgram.PrecisionBudget security bits) :
    1/(8*(Parameters.base security:ℝ)) ≤ (LocalPairProgram.activationApprox security bits:ℝ) := by
  have ha := FirstResponse.activation_lower_simple security
  have he := _p2mH130 security bits
  have hp : (8*(Parameters.modulus security:ℝ)+2)*(1/(2:ℝ)^bits) ≤
      1/(16*(Parameters.base security:ℝ)) := hprecision
  have hq := FirstResponse.modulus_pos security
  have hl := (abs_le.mp he).1
  have h0 : 0 ≤ 1/(2:ℝ)^bits := by positivity
  have hscale : 1/(4*(Parameters.base security:ℝ)) = 4*(1/(16*(Parameters.base security:ℝ))) := by ring
  have hscale' : 1/(8*(Parameters.base security:ℝ)) = 2*(1/(16*(Parameters.base security:ℝ))) := by ring
  nlinarith only [ha, hp, hq, hl, h0, hscale, hscale']
open _root_.P2M9e1cfc64 renaming h176 → _p2mH176
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h178 (security bits : ℕ) (score : ℕ → ℚ) (output : FirstHistogram.Palette security)
    (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color : FirstHistogram.Palette security, |(score color.val:ℝ)| ≤ bound)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ))) :
    |(current security bits score output.val:ℝ)-PrimaryTensorInverse.densityInverse security
      (fun color : FirstHistogram.Palette security => (score color.val:ℝ)) output| ≤
      errorConstant security*bound/(2:ℝ)^bits := by
  let epsilon : ℝ := 1/(2:ℝ)^bits
  let base : ℝ := Parameters.base security
  let q : ℝ := Parameters.modulus security
  let coefficient : ℝ := 64*base*Parameters.dimension security
  let approximate : ℕ → ℚ := fun color => primary security bits color*score color
  let realProfile : FirstHistogram.Palette security → ℝ :=
    fun color => (ProposalPrimary.primaryLaw security).weight color*(score color.val:ℝ)
  let approximateProfile : FirstHistogram.Palette security → ℝ := fun color => (approximate color.val:ℝ)
  let middle := (FirstResponse.responseEquiv security).symm approximateProfile output
  let realNumerator := (FirstResponse.responseEquiv security).symm realProfile output
  let approximateNumerator : ℝ := RationalFirstResponseProgram.inverse security bits approximate output.val
  let a : ℝ := (LocalPairProgram.activationApprox security bits:ℝ)*(primary security bits output.val:ℝ)
  let b : ℝ := DiffuseProfiles.activation security*(ProposalPrimary.primaryLaw security).weight output
  let lower : ℝ := 1/(32*base*q)
  have hq : 0 < q := FirstResponse.modulus_pos security
  have hbase : 0 < base := FirstResponse.base_pos security
  have he : 0 ≤ epsilon := by positivity
  have hc : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have hk : 0 ≤ inverseBound security := by unfold inverseBound; positivity
  have hi : 0 ≤ RationalFirstResponseProgram.inverseErrorConstant security := by
    unfold RationalFirstResponseProgram.inverseErrorConstant; positivity
  have hp (color : FirstHistogram.Palette security) :
      |(primary security bits color.val:ℝ)-(ProposalPrimary.primaryLaw security).weight color| ≤ coefficient*epsilon := by
    simpa only [ProposalPrimary.primaryLaw] using _p2mH392 security bits color hprecision hbudget
  have haProfile (color : FirstHistogram.Palette security) : |approximateProfile color| ≤ bound := by
    dsimp only [approximateProfile, approximate]
    rw [Rat.cast_mul]
    have hc0 : 0 ≤ (primary security bits color.val:ℝ) := (approximatePrimaryLaw security bits).nonneg color
    rw [abs_mul, abs_of_nonneg hc0]
    exact (mul_le_mul ((approximatePrimaryLaw security bits).atom_le_one color) (hscore color)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hrProfile (color : FirstHistogram.Palette security) : |realProfile color| ≤ bound := by
    rw [abs_mul, abs_of_nonneg ((ProposalPrimary.primaryLaw security).nonneg color)]
    exact (mul_le_mul ((ProposalPrimary.primaryLaw security).atom_le_one color) (hscore color)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hdProfile (color : FirstHistogram.Palette security) : |approximateProfile color-realProfile color| ≤ coefficient*epsilon*bound := by
    dsimp only [approximateProfile, approximate, realProfile]
    rw [Rat.cast_mul]
    rw [← sub_mul, abs_mul]
    exact mul_le_mul (hp color) (hscore color) (abs_nonneg _) (mul_nonneg hc he)
  have hn1 : |approximateNumerator-middle| ≤ RationalFirstResponseProgram.inverseErrorConstant security*bound*epsilon :=
    (_p2mH224 security bits approximate output bound hb haProfile hfirst).trans_eq (by dsimp only [epsilon]; ring)
  have hn2 : |middle-realNumerator| ≤ inverseBound security*(coefficient*epsilon*bound) := by
    have h := _p2mH177 security (approximateProfile-realProfile) (coefficient*epsilon*bound)
      (by positivity) hdProfile output
    simpa only [map_sub, Pi.sub_apply] using h
  have hn : |approximateNumerator-realNumerator| ≤
      (RationalFirstResponseProgram.inverseErrorConstant security+inverseBound security*coefficient)*bound*epsilon :=
    (abs_sub_le _ middle _).trans ((add_le_add hn1 hn2).trans_eq (by ring))
  have hnum : |realNumerator| ≤ inverseBound security*bound := _p2mH177 security realProfile bound hb hrProfile output
  have hpa := primary_lower security bits output
  have hpr : 1/(2*q) ≤ (ProposalPrimary.primaryLaw security).weight output := by
    simpa only [ProposalPrimary.primaryLaw] using ProposalPrimary.primaryProfile_atom_lower security output
  have haa := _p2mH176 security bits hfirst
  have har := FirstResponse.activation_lower_simple security
  have hap0 : 0 ≤ (primary security bits output.val:ℝ) := (approximatePrimaryLaw security bits).nonneg output
  have hpr0 := (ProposalPrimary.primaryLaw security).nonneg output
  have har0 := (DiffuseProfiles.activation_pos security).le
  have hal : lower ≤ a := by
    convert mul_le_mul haa hpa (by positivity) (LocalPairProgram.activationApprox_bounds security bits).1 using 1 <;>
      first | rfl | (dsimp only [lower, base, q, a]; ring)
  have hbl : lower ≤ b := by
    have hm := mul_le_mul har hpr (by positivity) (DiffuseProfiles.activation_pos security).le
    apply le_trans _ hm
    dsimp only [lower]
    have hprod : (1/(4*(Parameters.base security:ℝ)))*(1/(2*q)) = 1/(8*base*q) := by dsimp only [base]; ring
    rw [hprod]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hden : |a-b| ≤ (1/2+coefficient)*epsilon := by
    have herr := _p2mH130 security bits
    have hrate : |DiffuseProfiles.activation security| ≤ 1 := by
      rw [abs_of_pos (DiffuseProfiles.activation_pos security)]
      exact (DiffuseProfiles.activation_le_half security).trans (by norm_num)
    calc
      _ = |((LocalPairProgram.activationApprox security bits:ℝ)-DiffuseProfiles.activation security)*
          (primary security bits output.val:ℝ) + DiffuseProfiles.activation security*
          ((primary security bits output.val:ℝ)-(ProposalPrimary.primaryLaw security).weight output)| := by
        dsimp only [a, b]; congr 1; ring
      _ ≤ |(LocalPairProgram.activationApprox security bits:ℝ)-DiffuseProfiles.activation security| *
          (primary security bits output.val:ℝ) + |DiffuseProfiles.activation security| *
          |(primary security bits output.val:ℝ)-(ProposalPrimary.primaryLaw security).weight output| := by
        simpa only [abs_mul, abs_of_nonneg hap0] using abs_add_le
          (((LocalPairProgram.activationApprox security bits:ℝ)-DiffuseProfiles.activation security)*(primary security bits output.val:ℝ))
          (DiffuseProfiles.activation security*((primary security bits output.val:ℝ)-(ProposalPrimary.primaryLaw security).weight output))
      _ ≤ ((1/2:ℝ)*epsilon)*1 + 1*(coefficient*epsilon) :=
        add_le_add (mul_le_mul herr ((approximatePrimaryLaw security bits).atom_le_one output) hap0 (by positivity))
          (mul_le_mul hrate (hp output) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have hquot := _p2mH179 approximateNumerator realNumerator a b lower
    ((RationalFirstResponseProgram.inverseErrorConstant security+inverseBound security*coefficient)*bound*epsilon)
    ((1/2+coefficient)*epsilon) (inverseBound security*bound)
    (by dsimp only [lower]; positivity) hal hbl (by positivity) (by positivity) (by positivity) hn hden hnum
  have hformula : (current security bits score output.val:ℝ)-PrimaryTensorInverse.densityInverse security
      (fun color : FirstHistogram.Palette security => (score color.val:ℝ)) output = approximateNumerator/a-realNumerator/b := by
    simp only [current, Rat.cast_div, Rat.cast_mul, PrimaryTensorInverse.densityInverse_apply]
    change approximateNumerator/a - (DiffuseProfiles.activation security)⁻¹*realNumerator/
      (ProposalPrimary.primaryLaw security).weight output = _
    dsimp only [b]
    ring
  rw [hformula]
  apply hquot.trans_eq
  dsimp only [lower, base, q, coefficient, epsilon, errorConstant]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
  ring_nf
  simp only [inv_inv]
  ring
open _root_.P2M9e1cfc64 renaming h178 → _p2mH178
end
open _root_.P2M9e1cfc64 renaming h176 → _p2mH176
open _root_.P2M9e1cfc64 renaming h177 → _p2mH177
open _root_.P2M9e1cfc64 renaming h178 → _p2mH178
open _root_.P2M9e1cfc64 renaming h179 → _p2mH179
end CurrentAFT.RationalDensityInverseProgram
open _root_.P2M9e1cfc64 renaming h176 → _p2mH176
open _root_.P2M9e1cfc64 renaming h177 → _p2mH177
open _root_.P2M9e1cfc64 renaming h178 → _p2mH178
open _root_.P2M9e1cfc64 renaming h179 → _p2mH179
end
open _root_.P2M9e1cfc64 renaming h179 → _p2mH179
open _root_.P2M9e1cfc64 renaming h176 → _p2mH176
open _root_.P2M9e1cfc64 renaming h178 → _p2mH178
open _root_.P2M9e1cfc64 renaming h177 → _p2mH177
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
theorem _root_.P2M9e1cfc64.h455 (security : ℕ) : 0 ≤ actualBound security := by
  unfold actualBound RationalDensityInverseProgram.inverseBound
  positivity
open _root_.P2M9e1cfc64 renaming h455 → _p2mH455
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h462 (security : ℕ) : 0 ≤ RationalDensityInverseProgram.errorConstant security := by
  unfold RationalDensityInverseProgram.errorConstant RationalDensityInverseProgram.inverseBound
    RationalFirstResponseProgram.inverseErrorConstant
  positivity
open _root_.P2M9e1cfc64 renaming h462 → _p2mH462
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h456 (security : ℕ) (input : Palette security → ℝ) (bound : ℝ)
    (hb : 0 ≤ bound) (hinput : ∀ color, |input color| ≤ bound) (output : Palette security) :
    |PrimaryTensorInverse.densityInverse security input output| ≤ actualBound security * bound := by
  let profile := fun color : Palette security => (primaryLaw security).weight color * input color
  have hprofile (color : Palette security) : |profile color| ≤ bound := by
    dsimp only [profile]
    rw [abs_mul, abs_of_nonneg ((primaryLaw security).nonneg color)]
    exact (mul_le_mul ((primaryLaw security).atom_le_one color) (hinput color) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hnum := _p2mH177 security profile bound hb hprofile output
  have hb0 := FirstResponse.base_pos security
  have hq0 := FirstResponse.modulus_pos security
  have hp : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
    simpa only [primaryLaw] using primaryProfile_atom_lower security output
  have hden : 1 / (8 * (Parameters.base security : ℝ) * Parameters.modulus security) ≤
      activation security * (primaryLaw security).weight output := by
    calc
      _ = (1 / (4 * (Parameters.base security : ℝ))) * (1 / (2 * (Parameters.modulus security : ℝ))) := by ring
      _ ≤ _ := mul_le_mul (FirstResponse.activation_lower_simple security) hp (by positivity) (activation_pos security).le
  have hdenpos : 0 < activation security * (primaryLaw security).weight output :=
    mul_pos (activation_pos security) (primaryReference_positive security output)
  have hformula : PrimaryTensorInverse.densityInverse security input output =
      (FirstResponse.responseEquiv security).symm profile output /
        (activation security * (primaryLaw security).weight output) := by
    rw [PrimaryTensorInverse.densityInverse_apply]
    dsimp only [profile]
    ring
  rw [hformula, abs_div, abs_of_pos hdenpos]
  calc
    _ ≤ (RationalDensityInverseProgram.inverseBound security * bound) /
        (activation security * (primaryLaw security).weight output) :=
      div_le_div_of_nonneg_right hnum hdenpos.le
    _ ≤ (RationalDensityInverseProgram.inverseBound security * bound) /
        (1 / (8 * (Parameters.base security : ℝ) * Parameters.modulus security)) :=
      div_le_div_of_nonneg_left (by unfold RationalDensityInverseProgram.inverseBound; positivity)
        (by positivity) hden
    _ = _ := by unfold actualBound; ring_nf; simp only [inv_inv]
open _root_.P2M9e1cfc64 renaming h456 → _p2mH456
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h461 (security bits : ℕ) (source output : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(entry security bits source.val output.val : ℝ) -
      PrimaryTensorInverse.densityInverse security (Pi.single source 1) output| ≤
        RationalDensityInverseProgram.errorConstant security * (1 / (2 : ℝ)^bits) := by
  have hsingle : (fun color : Palette security =>
      ((if color.val = source.val then 1 else 0 : ℚ) : ℝ)) = Pi.single source 1 := by
    funext color
    by_cases hequal : color = source
    · subst color; simp
    · have hne : color.val ≠ source.val := fun h => hequal (Fin.ext h)
      simp [hne, hequal]
  have h := _p2mH178 security bits
    (fun color => if color = source.val then 1 else 0) output 1 (by norm_num)
    (fun color => by split_ifs <;> norm_num) hfirst hprecision hbudget
  try dsimp only at h
  rw [hsingle] at h
  simpa only [entry, mul_one, div_eq_mul_inv, one_div, one_mul] using h
open _root_.P2M9e1cfc64 renaming h461 → _p2mH461
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h463 (security : ℕ) : 1 ≤ factorBound security := by
  unfold factorBound
  linarith [_p2mH455 security, _p2mH462 security]
open _root_.P2M9e1cfc64 renaming h463 → _p2mH463
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h460 (security bits : ℕ) (source output : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(entry security bits source.val output.val : ℝ)| ≤ factorBound security ∧
    |PrimaryTensorInverse.densityInverse security (Pi.single source 1) output| ≤ factorBound security := by
  have he := _p2mH461 security bits source output hfirst hprecision hbudget
  have ht := _p2mH456 security (Pi.single source 1) 1 (by norm_num)
    (fun color => by simp only [Pi.single_apply]; split_ifs <;> norm_num) output
  simp only [mul_one] at ht
  have heps : 1 / (2 : ℝ)^bits ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^bits)).mpr
    simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2^bits)
  have htri := abs_add_le
    ((entry security bits source.val output.val : ℝ) - PrimaryTensorInverse.densityInverse security (Pi.single source 1) output)
    (PrimaryTensorInverse.densityInverse security (Pi.single source 1) output)
  rw [sub_add_cancel] at htri
  have hsmall := mul_le_mul_of_nonneg_left heps (_p2mH462 security)
  unfold factorBound
  constructor <;> linarith [_p2mH455 security, _p2mH462 security]
open _root_.P2M9e1cfc64 renaming h460 → _p2mH460
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h464 {Index : Type*} [DecidableEq Index]
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
open _root_.P2M9e1cfc64 renaming h464 → _p2mH464
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h458 (security bits degree : ℕ) (input : (Fin degree → ℕ) → ℚ)
    (output : Fin degree → Palette security) :
    (current security bits degree input (fun index => (output index).val) : ℝ) =
      ∑ source : Fin degree → Palette security, (input (fun index => (source index).val) : ℝ) *
        ∏ index, (entry security bits (source index).val (output index).val : ℝ) := by
  unfold current
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_prod]
  apply Finset.sum_congr (by ext; simp)
  intro source _
  rfl
open _root_.P2M9e1cfc64 renaming h458 → _p2mH458
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h459 (security bits degree : ℕ) (input : (Fin degree → ℕ) → ℚ)
    (bound : ℝ) (hb : 0 ≤ bound)
    (hinput : ∀ source : Fin degree → Palette security, |(input (fun index => (source index).val) : ℝ)| ≤ bound)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin degree → Palette security) :
    |(current security bits degree input (fun index => (output index).val) : ℝ) -
      PrimaryTensorInverse.tensorInverse security degree
        (fun source => (input (fun index => (source index).val) : ℝ)) output| ≤
          tensorErrorConstant security degree * bound * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH458]
  change |(∑ source : Fin degree → Palette security, _) -
    TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security)
      (fun source => (input (fun index => (source index).val) : ℝ)) output| ≤ _
  rw [TensorChannel.apply_formula_instance, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _source : Fin degree → Palette security,
        bound * ((degree : ℝ) * (RationalDensityInverseProgram.errorConstant security * (1 / (2 : ℝ)^bits)) *
          (factorBound security)^degree) := by
      apply Finset.sum_le_sum
      intro source _
      rw [← mul_sub, abs_mul]
      have hprod := _p2mH464 Finset.univ
        (fun index : Fin degree => (entry security bits (source index).val (output index).val : ℝ))
        (fun index => PrimaryTensorInverse.densityInverse security (Pi.single (source index) 1) (output index))
        (factorBound security) (RationalDensityInverseProgram.errorConstant security * (1 / (2 : ℝ)^bits))
        (_p2mH463 security) (by positivity [_p2mH462 security])
        (fun index _ => (_p2mH460 security bits _ _ hfirst hprecision hbudget).1)
        (fun index _ => (_p2mH460 security bits _ _ hfirst hprecision hbudget).2)
        (fun index _ => _p2mH461 security bits _ _ hfirst hprecision hbudget)
      simp only [Finset.card_univ, Fintype.card_fin] at hprod
      exact mul_le_mul (hinput source) hprod (abs_nonneg _) hb
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      unfold tensorErrorConstant
      push_cast
      ring
open _root_.P2M9e1cfc64 renaming h459 → _p2mH459
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h457 (security degree : ℕ)
    (first second : (Fin degree → Palette security) → ℝ) (error : ℝ)
    (he : 0 ≤ error) (hdiff : ∀ source, |first source - second source| ≤ error)
    (output : Fin degree → Palette security) :
    |PrimaryTensorInverse.tensorInverse security degree first output -
      PrimaryTensorInverse.tensorInverse security degree second output| ≤
        (Parameters.modulus security : ℝ)^degree * (actualBound security)^degree * error := by
  change |TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security) first output -
    TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security) second output| ≤ _
  rw [TensorChannel.apply_formula_instance, TensorChannel.apply_formula_instance, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _source : Fin degree → Palette security, error * (actualBound security)^degree := by
      apply Finset.sum_le_sum
      intro source _
      rw [← sub_mul, abs_mul]
      apply mul_le_mul (hdiff source) _ (abs_nonneg _) he
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _index : Fin degree, actualBound security :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun index _ => by
            simpa only [mul_one] using _p2mH456 security (Pi.single (source index) 1) 1
              (by norm_num) (fun color => by simp only [Pi.single_apply]; split_ifs <;> norm_num) (output index))
        _ = _ := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
open _root_.P2M9e1cfc64 renaming h457 → _p2mH457
end
open _root_.P2M9e1cfc64 renaming h455 → _p2mH455
open _root_.P2M9e1cfc64 renaming h456 → _p2mH456
open _root_.P2M9e1cfc64 renaming h457 → _p2mH457
open _root_.P2M9e1cfc64 renaming h458 → _p2mH458
open _root_.P2M9e1cfc64 renaming h459 → _p2mH459
open _root_.P2M9e1cfc64 renaming h460 → _p2mH460
open _root_.P2M9e1cfc64 renaming h461 → _p2mH461
open _root_.P2M9e1cfc64 renaming h462 → _p2mH462
open _root_.P2M9e1cfc64 renaming h463 → _p2mH463
open _root_.P2M9e1cfc64 renaming h464 → _p2mH464
end CurrentAFT.RationalTensorInverseProgram
open _root_.P2M9e1cfc64 renaming h455 → _p2mH455
open _root_.P2M9e1cfc64 renaming h456 → _p2mH456
open _root_.P2M9e1cfc64 renaming h457 → _p2mH457
open _root_.P2M9e1cfc64 renaming h458 → _p2mH458
open _root_.P2M9e1cfc64 renaming h459 → _p2mH459
open _root_.P2M9e1cfc64 renaming h460 → _p2mH460
open _root_.P2M9e1cfc64 renaming h461 → _p2mH461
open _root_.P2M9e1cfc64 renaming h462 → _p2mH462
open _root_.P2M9e1cfc64 renaming h463 → _p2mH463
open _root_.P2M9e1cfc64 renaming h464 → _p2mH464
end
open _root_.P2M9e1cfc64 renaming h459 → _p2mH459
open _root_.P2M9e1cfc64 renaming h456 → _p2mH456
open _root_.P2M9e1cfc64 renaming h461 → _p2mH461
open _root_.P2M9e1cfc64 renaming h457 → _p2mH457
open _root_.P2M9e1cfc64 renaming h462 → _p2mH462
open _root_.P2M9e1cfc64 renaming h464 → _p2mH464
open _root_.P2M9e1cfc64 renaming h463 → _p2mH463
open _root_.P2M9e1cfc64 renaming h455 → _p2mH455
open _root_.P2M9e1cfc64 renaming h460 → _p2mH460
open _root_.P2M9e1cfc64 renaming h458 → _p2mH458
section
namespace CurrentAFT.RationalLegCoefficientExtraction
open AFT DiffuseProfiles ProposalPrimary ActualControls
  ControlCoordinates ControlProduct
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalLegCoefficientExtraction.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalLegCoefficientExtraction.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h244 (security degree : ℕ)
    (kernel : (Fin degree → Palette security) → ℝ) (permutation : Equiv.Perm (Fin degree))
    (output : Fin degree → Palette security) :
    PrimaryTensorInverse.tensorInverse security degree kernel (output ∘ permutation) =
      PrimaryTensorInverse.tensorInverse security degree (fun word => kernel (word ∘ permutation)) output := by
  change TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security) kernel (output ∘ permutation) =
    TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security) (fun word => kernel (word ∘ permutation)) output
  rw [TensorChannel.apply_formula_instance, TensorChannel.apply_formula_instance]
  rw [← (PrimaryTensorInverse.wordPermutation (Input := Palette security) degree permutation).sum_comp]
  apply Finset.sum_congr rfl
  intro source _
  congr 1
  exact Equiv.prod_comp permutation (fun index =>
    PrimaryTensorInverse.densityInverse security (Pi.single (source index) 1) (output index))
open _root_.P2M9e1cfc64 renaming h244 → _p2mH244
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h240 (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) :
    orderedDensity security mass selected = fun output =>
      RootLegCoefficientFamily.selectedDensity security selected.card mass selected (by simp)
        (output ∘ orderPermutation selected) := by
  funext output
  unfold orderedDensity RootLegCoefficientFamily.selectedDensity
  congr 1
  funext slot
  simp only [Function.comp_apply, orderPermutation, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl
open _root_.P2M9e1cfc64 renaming h240 → _p2mH240
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h243 (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) :
    (RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val =
      symmetrize (fun (colors : Fin selected.card → Palette security) (_ : Fin 0 → SafePalette security) =>
        PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security mass selected) colors) := by
  let raw : DensityKernel (Primary := Palette security) (Body := SafePalette security) selected.card 0 :=
    fun colors _ => RootLegCoefficientFamily.normalizedSelectedDensity security selected.card mass selected (by simp) colors
  have hraw : (fun (colors : Fin selected.card → Palette security) (_ : Fin 0 → SafePalette security) =>
      PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security mass selected) colors) =
      reindexKernel (orderPermutation selected) (Equiv.refl (Fin 0)) raw := by
    funext colors centers
    rw [_p2mH240, ← _p2mH244]
    rfl
  rw [hraw, symmetrize_reindex_permutations]
  rfl
open _root_.P2M9e1cfc64 renaming h243 → _p2mH243
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h239 (security : ℕ) (source output : Palette security) :
    |(if source = output then (1 : ℝ) else 0) - 1 / (Parameters.modulus security : ℝ)| ≤ 1 := by
  have hq : (1 : ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_spec security).2.two_le.trans' (by omega)
  have hl : 0 ≤ 1 / (Parameters.modulus security : ℝ) := by positivity
  have hu : 1 / (Parameters.modulus security : ℝ) ≤ 1 :=
    (div_le_iff₀ (FirstResponse.modulus_pos security)).mpr (by simpa using hq)
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2M9e1cfc64 renaming h239 → _p2mH239
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h232 (security bits : ℕ) (source output : Palette security) :
    (atom security bits source.val output.val : ℝ) =
      ((if source = output then (1 : ℝ) else 0) - 1 / (Parameters.modulus security : ℝ)) /
        (RationalProposalProgram.approximatePrimaryLaw security bits).weight output := by
  unfold atom
  rw [PublicParameterProgram.modulus_value]
  by_cases hequal : source = output
  · subst output
    simp only [if_true, Rat.cast_div, Rat.cast_sub, Rat.cast_one, Rat.cast_natCast]
    rfl
  · have hne : source.val ≠ output.val := fun h => hequal (Fin.ext h)
    simp only [if_neg hne, if_neg hequal, Rat.cast_div, Rat.cast_sub, Rat.cast_zero, Rat.cast_one, Rat.cast_natCast]
    rfl
open _root_.P2M9e1cfc64 renaming h232 → _p2mH232
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h231 (security bits : ℕ) (source output : Palette security) :
    |(atom security bits source.val output.val : ℝ)| ≤ 4 * (Parameters.modulus security : ℝ) := by
  have hq0 := FirstResponse.modulus_pos security
  have hp := RationalProposalProgram.primary_lower security bits output
  have hpos : 0 < (RationalProposalProgram.approximatePrimaryLaw security bits).weight output :=
    (by positivity : (0 : ℝ) < 1 / (4 * (Parameters.modulus security : ℝ))).trans_le hp
  rw [_p2mH232, abs_div, abs_of_pos hpos]
  calc
    _ ≤ 1 / (RationalProposalProgram.approximatePrimaryLaw security bits).weight output :=
      div_le_div_of_nonneg_right (_p2mH239 security source output) hpos.le
    _ ≤ 1 / (1 / (4 * (Parameters.modulus security : ℝ))) :=
      one_div_le_one_div_of_le (by positivity) hp
    _ = _ := by simp only [one_div, inv_inv]
open _root_.P2M9e1cfc64 renaming h231 → _p2mH231
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h233 (security bits : ℕ) (source output : Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(atom security bits source.val output.val : ℝ) -
      MixedKernel.referenceAtom (primaryLaw security) (LocalReferenceEnergy.uniformReference security) source output| ≤
        atomErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have hq0 := FirstResponse.modulus_pos security
  have hlo : 1 / (4 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
    have h : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
      simpa only [primaryLaw] using primaryProfile_atom_lower security output
    have hscale : 1 / (4 * (Parameters.modulus security : ℝ)) ≤ 1 / (2 * (Parameters.modulus security : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    exact hscale.trans h
  have hp : |(RationalProposalProgram.approximatePrimaryLaw security bits).weight output - (primaryLaw security).weight output| ≤
      RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits) := by
    simpa only [RationalProposalProgram.approximatePrimaryLaw, primaryLaw, RationalRootMassProgram.primaryErrorConstant] using
      _p2mH392 security bits output hprecision hbudget
  rw [_p2mH232, MixedKernel.referenceAtom_eq, LocalReferenceEnergy.uniformReference_weight]
  have h := _p2mH179
    ((if source = output then (1 : ℝ) else 0) - 1 / (Parameters.modulus security : ℝ))
    ((if source = output then (1 : ℝ) else 0) - 1 / (Parameters.modulus security : ℝ))
    ((RationalProposalProgram.approximatePrimaryLaw security bits).weight output)
    ((primaryLaw security).weight output)
    (1 / (4 * (Parameters.modulus security : ℝ))) 0
    (RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits)) 1
    (by positivity) (RationalProposalProgram.primary_lower security bits output) hlo (by norm_num)
    (by unfold RationalRootMassProgram.primaryErrorConstant; positivity) (by norm_num)
    (by simp) hp (_p2mH239 security source output)
  apply h.trans_eq
  unfold atomErrorConstant
  ring_nf
  simp only [inv_inv]
open _root_.P2M9e1cfc64 renaming h233 → _p2mH233
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h229 (security : ℕ) (source output : Palette security) :
    |MixedKernel.referenceAtom (primaryLaw security) (LocalReferenceEnergy.uniformReference security) source output| ≤
      4 * (Parameters.modulus security : ℝ) := by
  have hq0 := FirstResponse.modulus_pos security
  have hp : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
    simpa only [primaryLaw] using primaryProfile_atom_lower security output
  rw [MixedKernel.referenceAtom_eq, LocalReferenceEnergy.uniformReference_weight, abs_div,
    abs_of_pos (primaryReference_positive security output)]
  calc
    _ ≤ 1 / (primaryLaw security).weight output :=
      div_le_div_of_nonneg_right (_p2mH239 security source output) (primaryReference_positive security output).le
    _ ≤ 1 / (1 / (2 * (Parameters.modulus security : ℝ))) :=
      one_div_le_one_div_of_le (by positivity) hp
    _ ≤ _ := by simp only [one_div, inv_inv]; linarith
open _root_.P2M9e1cfc64 renaming h229 → _p2mH229
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h235 (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ) (selected : Finset (Fin 3))
    (output : Fin selected.card → Palette security) :
    (density security bits mass selected (fun index => (output index).val) : ℝ) =
      ∑ source : Fin 3 → Palette security, (mass (fun index => (source index).val) : ℝ) *
        ∏ slot : selected, (atom security bits (source slot.val).val (output (slotNumber selected slot)).val : ℝ) := by
  unfold density
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_prod]
  apply Finset.sum_congr (by ext; simp)
  intro source _
  congr 1
open _root_.P2M9e1cfc64 renaming h235 → _p2mH235
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h237 (bits : ℕ) : 1 / (2 : ℝ)^bits ≤ 1 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^bits)).mpr
  simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2^bits)
open _root_.P2M9e1cfc64 renaming h237 → _p2mH237
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h234 (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ)
    (actualMass : (Fin 3 → Palette security) → ℝ) (selected : Finset (Fin 3))
    (massBound massError : ℝ) (hM : 0 ≤ massBound) (hE : 0 ≤ massError)
    (hmass : ∀ source, |actualMass source| ≤ massBound)
    (hdiff : ∀ source, |(mass (fun index => (source index).val) : ℝ) - actualMass source| ≤
      massError * (1 / (2 : ℝ)^bits)) (output : Fin selected.card → Palette security) :
    |(density security bits mass selected (fun index => (output index).val) : ℝ)| ≤
      extractionBound security selected.card massBound massError := by
  rw [_p2mH235]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _source : Fin 3 → Palette security,
        (massBound + massError) * (4 * (Parameters.modulus security : ℝ))^selected.card := by
      apply Finset.sum_le_sum
      intro source _
      have happrox : |(mass (fun index => (source index).val) : ℝ)| ≤ massBound + massError := by
        have h := abs_add_le ((mass (fun index => (source index).val) : ℝ) - actualMass source) (actualMass source)
        rw [sub_add_cancel] at h
        have hs := mul_le_mul_of_nonneg_left (_p2mH237 bits) hE
        linarith [hdiff source, hmass source]
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul happrox _ (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
      calc
        _ ≤ ∏ _slot : selected, 4 * (Parameters.modulus security : ℝ) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun slot _ => _p2mH231 security bits _ _)
        _ = _ := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      unfold extractionBound
      push_cast
      ring
open _root_.P2M9e1cfc64 renaming h234 → _p2mH234
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h236 (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ)
    (actualMass : (Fin 3 → Palette security) → ℝ) (selected : Finset (Fin 3))
    (massBound massError : ℝ) (hM : 0 ≤ massBound) (hE : 0 ≤ massError)
    (hmass : ∀ source, |actualMass source| ≤ massBound)
    (hdiff : ∀ source, |(mass (fun index => (source index).val) : ℝ) - actualMass source| ≤
      massError * (1 / (2 : ℝ)^bits))
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) :
    |(density security bits mass selected (fun index => (output index).val) : ℝ) -
      orderedDensity security actualMass selected output| ≤
        extractionError security selected.card massBound massError * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let K : ℝ := 4 * Parameters.modulus security
  have hK : 1 ≤ K := by
    have hq : (2 : ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.two_le
    dsimp only [K]
    linarith
  have hA : 0 ≤ atomErrorConstant security := by
    unfold atomErrorConstant RationalRootMassProgram.primaryErrorConstant
    positivity
  rw [_p2mH235]
  unfold orderedDensity LocalTensors.referenceRestrictedComponent
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _source : Fin 3 → Palette security,
        (massError + massBound * selected.card * atomErrorConstant security) * K^selected.card * epsilon := by
      apply Finset.sum_le_sum
      intro source _
      let approxAtom := fun slot : selected =>
        (atom security bits (source slot.val).val (output (slotNumber selected slot)).val : ℝ)
      let trueAtom := fun slot : selected => MixedKernel.referenceAtom (primaryLaw security)
        (LocalReferenceEnergy.uniformReference security) (source slot.val) (output (slotNumber selected slot))
      have haprod : |∏ slot : selected, approxAtom slot| ≤ K^selected.card := by
        rw [Finset.abs_prod]
        calc
          _ ≤ ∏ _slot : selected, K := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
            (fun slot _ => _p2mH231 security bits _ _)
          _ = _ := by simp
      have hprod := _p2mH464 Finset.univ approxAtom trueAtom K
        (atomErrorConstant security * epsilon) hK (by positivity)
        (fun slot _ => _p2mH231 security bits _ _)
        (fun slot _ => _p2mH229 security _ _)
        (fun slot _ => _p2mH233 security bits _ _ hprecision hbudget)
      simp only [Finset.card_univ, Fintype.card_coe] at hprod
      change |(mass (fun index => (source index).val) : ℝ) * (∏ slot, approxAtom slot) -
        actualMass source * (∏ slot, trueAtom slot)| ≤ _
      calc
        _ = |((mass (fun index => (source index).val) : ℝ) - actualMass source) * (∏ slot, approxAtom slot) +
          actualMass source * ((∏ slot, approxAtom slot) - ∏ slot, trueAtom slot)| := by congr 1; ring
        _ ≤ |(mass (fun index => (source index).val) : ℝ) - actualMass source| * |∏ slot, approxAtom slot| +
          |actualMass source| * |(∏ slot, approxAtom slot) - ∏ slot, trueAtom slot| := by
            simpa only [abs_mul] using abs_add_le
              (((mass (fun index => (source index).val) : ℝ) - actualMass source) * (∏ slot, approxAtom slot))
              (actualMass source * ((∏ slot, approxAtom slot) - ∏ slot, trueAtom slot))
        _ ≤ (massError * epsilon) * K^selected.card +
          massBound * ((selected.card : ℝ) * (atomErrorConstant security * epsilon) * K^selected.card) :=
            add_le_add (mul_le_mul (hdiff source) haprod (abs_nonneg _) (by positivity))
              (mul_le_mul (hmass source) hprod (abs_nonneg _) hM)
        _ = _ := by ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      unfold extractionError
      dsimp only [K, epsilon]
      push_cast
      ring
open _root_.P2M9e1cfc64 renaming h236 → _p2mH236
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h238 (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ)
    (actualMass : (Fin 3 → Palette security) → ℝ) (selected : Finset (Fin 3))
    (massBound massError : ℝ) (hM : 0 ≤ massBound) (hE : 0 ≤ massError)
    (hmass : ∀ source, |actualMass source| ≤ massBound)
    (hdiff : ∀ source, |(mass (fun index => (source index).val) : ℝ) - actualMass source| ≤
      massError * (1 / (2 : ℝ)^bits))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) :
    |(normalized security bits mass selected (fun index => (output index).val) : ℝ) -
      PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security actualMass selected) output| ≤
        normalizedError security selected.card massBound massError * (1 / (2 : ℝ)^bits) := by
  let approximate := fun source : Fin selected.card → Palette security =>
    (density security bits mass selected (fun index => (source index).val) : ℝ)
  have hbound : 0 ≤ extractionBound security selected.card massBound massError := by
    unfold extractionBound
    positivity
  have he : 0 ≤ extractionError security selected.card massBound massError := by
    unfold extractionError atomErrorConstant RationalRootMassProgram.primaryErrorConstant
    positivity
  have hprogram := _p2mH459 security bits selected.card
    (density security bits mass selected) (extractionBound security selected.card massBound massError) hbound
    (fun source => _p2mH234 security bits mass actualMass selected massBound massError hM hE hmass hdiff source)
    hfirst hprecision hbudget output
  have hreal := _p2mH457 security selected.card
    approximate (orderedDensity security actualMass selected)
    (extractionError security selected.card massBound massError * (1 / (2 : ℝ)^bits)) (by positivity)
    (fun source => _p2mH236 security bits mass actualMass selected massBound massError hM hE hmass hdiff
      hprecision hbudget source) output
  unfold normalized
  calc
    _ ≤ |(RationalTensorInverseProgram.current security bits selected.card (density security bits mass selected)
          (fun index => (output index).val) : ℝ) -
        PrimaryTensorInverse.tensorInverse security selected.card approximate output| +
      |PrimaryTensorInverse.tensorInverse security selected.card approximate output -
        PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security actualMass selected) output| :=
      abs_sub_le _ _ _
    _ ≤ _ := add_le_add hprogram hreal
    _ = _ := by unfold normalizedError; ring
open _root_.P2M9e1cfc64 renaming h238 → _p2mH238
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h241 (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ)
    (selected : Finset (Fin 3)) (output : Fin selected.card → Palette security) :
    (selectedKernel security bits mass selected (fun index => (output index).val) : ℝ) =
      (FiniteDist.uniform (Equiv.Perm (Fin selected.card))).expectation (fun permutation =>
        (normalized security bits mass selected (fun index => (output (permutation index)).val) : ℝ)) := by
  simp only [selectedKernel, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_sum]
  unfold FiniteDist.expectation
  simp only [FiniteDist.uniform_weight, ← Finset.mul_sum, Fintype.card_perm, Fintype.card_fin, one_div]
  apply congrArg (fun value : ℝ => ((selected.card.factorial : ℝ)⁻¹) * value)
  apply Finset.sum_congr (by ext; simp)
  intro permutation _
  rfl
open _root_.P2M9e1cfc64 renaming h241 → _p2mH241
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h230 (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (output : Fin selected.card → Palette security)
    (body : Fin 0 → SafePalette security) :
    (RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output body =
      (FiniteDist.uniform (Equiv.Perm (Fin selected.card))).expectation (fun permutation =>
        PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security mass selected)
          (output ∘ permutation)) := by
  rw [_p2mH243, ControlProduct.symmetrize_apply]
  simp only [Fintype.card_perm, Fintype.card_fin, Nat.factorial_zero, Nat.cast_one, inv_one, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_mul]
  unfold FiniteDist.expectation
  simp only [FiniteDist.uniform_weight, ← Finset.mul_sum, Fintype.card_perm, Fintype.card_fin]
open _root_.P2M9e1cfc64 renaming h230 → _p2mH230
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h242 (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ)
    (actualMass : (Fin 3 → Palette security) → ℝ) (selected : Finset (Fin 3))
    (massBound massError : ℝ) (hM : 0 ≤ massBound) (hE : 0 ≤ massError)
    (hmass : ∀ source, |actualMass source| ≤ massBound)
    (hdiff : ∀ source, |(mass (fun index => (source index).val) : ℝ) - actualMass source| ≤
      massError * (1 / (2 : ℝ)^bits))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) (body : Fin 0 → SafePalette security) :
    |(selectedKernel security bits mass selected (fun index => (output index).val) : ℝ) -
      (RootLegCoefficientFamily.selectedKernel security selected.card actualMass selected (by simp)).val output body| ≤
        normalizedError security selected.card massBound massError * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH241, _p2mH230]
  unfold FiniteDist.expectation
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ permutation : Equiv.Perm (Fin selected.card),
        (FiniteDist.uniform (Equiv.Perm (Fin selected.card))).weight permutation *
          (normalizedError security selected.card massBound massError * (1 / (2 : ℝ)^bits)) := by
      apply Finset.sum_le_sum
      intro permutation _
      rw [← mul_sub, abs_mul, abs_of_nonneg (FiniteDist.nonneg _ _)]
      exact mul_le_mul_of_nonneg_left
        (_p2mH238 security bits mass actualMass selected massBound massError hM hE hmass hdiff
          hfirst hprecision hbudget (output ∘ permutation)) (FiniteDist.nonneg _ _)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
open _root_.P2M9e1cfc64 renaming h242 → _p2mH242
end
open _root_.P2M9e1cfc64 renaming h229 → _p2mH229
open _root_.P2M9e1cfc64 renaming h230 → _p2mH230
open _root_.P2M9e1cfc64 renaming h231 → _p2mH231
open _root_.P2M9e1cfc64 renaming h232 → _p2mH232
open _root_.P2M9e1cfc64 renaming h233 → _p2mH233
open _root_.P2M9e1cfc64 renaming h234 → _p2mH234
open _root_.P2M9e1cfc64 renaming h235 → _p2mH235
open _root_.P2M9e1cfc64 renaming h236 → _p2mH236
open _root_.P2M9e1cfc64 renaming h237 → _p2mH237
open _root_.P2M9e1cfc64 renaming h238 → _p2mH238
open _root_.P2M9e1cfc64 renaming h239 → _p2mH239
open _root_.P2M9e1cfc64 renaming h240 → _p2mH240
open _root_.P2M9e1cfc64 renaming h241 → _p2mH241
open _root_.P2M9e1cfc64 renaming h242 → _p2mH242
open _root_.P2M9e1cfc64 renaming h243 → _p2mH243
open _root_.P2M9e1cfc64 renaming h244 → _p2mH244
end CurrentAFT.RationalLegCoefficientExtraction
open _root_.P2M9e1cfc64 renaming h229 → _p2mH229
open _root_.P2M9e1cfc64 renaming h230 → _p2mH230
open _root_.P2M9e1cfc64 renaming h231 → _p2mH231
open _root_.P2M9e1cfc64 renaming h232 → _p2mH232
open _root_.P2M9e1cfc64 renaming h233 → _p2mH233
open _root_.P2M9e1cfc64 renaming h234 → _p2mH234
open _root_.P2M9e1cfc64 renaming h235 → _p2mH235
open _root_.P2M9e1cfc64 renaming h236 → _p2mH236
open _root_.P2M9e1cfc64 renaming h237 → _p2mH237
open _root_.P2M9e1cfc64 renaming h238 → _p2mH238
open _root_.P2M9e1cfc64 renaming h239 → _p2mH239
open _root_.P2M9e1cfc64 renaming h240 → _p2mH240
open _root_.P2M9e1cfc64 renaming h241 → _p2mH241
open _root_.P2M9e1cfc64 renaming h242 → _p2mH242
open _root_.P2M9e1cfc64 renaming h243 → _p2mH243
open _root_.P2M9e1cfc64 renaming h244 → _p2mH244
end
open _root_.P2M9e1cfc64 renaming h239 → _p2mH239
open _root_.P2M9e1cfc64 renaming h234 → _p2mH234
open _root_.P2M9e1cfc64 renaming h244 → _p2mH244
open _root_.P2M9e1cfc64 renaming h229 → _p2mH229
open _root_.P2M9e1cfc64 renaming h243 → _p2mH243
open _root_.P2M9e1cfc64 renaming h241 → _p2mH241
open _root_.P2M9e1cfc64 renaming h231 → _p2mH231
open _root_.P2M9e1cfc64 renaming h232 → _p2mH232
open _root_.P2M9e1cfc64 renaming h233 → _p2mH233
open _root_.P2M9e1cfc64 renaming h237 → _p2mH237
open _root_.P2M9e1cfc64 renaming h235 → _p2mH235
open _root_.P2M9e1cfc64 renaming h230 → _p2mH230
open _root_.P2M9e1cfc64 renaming h240 → _p2mH240
open _root_.P2M9e1cfc64 renaming h236 → _p2mH236
open _root_.P2M9e1cfc64 renaming h242 → _p2mH242
open _root_.P2M9e1cfc64 renaming h238 → _p2mH238
section
namespace CurrentAFT.RationalLegMassProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
open PositiveFirstCoefficient (positiveTripleLaw positiveFourLaw consEquiv)
open PairedReferenceEnergy (compensatorAt)
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalLegMassProgram.classicalFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw PublicParameterProgram.modulus
attribute [local irreducible] rootReference ActualBlockFock.primaryLawAt
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h253 (security bits : ℕ) (root : ℤ) (word : Fin 3 → ℕ) :
    atRoot security bits root word =
      ∑ scalar : Window ((security + 2)^2 - 1),
        RationalProposalProgram.gaussianWeight security ((security + 2)^2 - 1) bits scalar *
          fixed security bits root scalar.val word := by
  unfold atRoot
  exact (FiniteConvolutionProgram.windowIndexEquiv ((security + 2)^2 - 1)).sum_comp
    (fun scalar : Window ((security + 2)^2 - 1) =>
      RationalProposalProgram.gaussianWeight security ((security + 2)^2 - 1) bits scalar *
        fixed security bits root scalar.val word)
open _root_.P2M9e1cfc64 renaming h253 → _p2mH253
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h259 (security : ℕ) (root : ℤ) (scalar : FirstHistogram.Scalar security)
    (word : Fin 3 → Palette security) :
    (∑ compensator : Palette security,
      (positiveFourLaw security 0 root scalar).weight (Fin.cons compensator word)) =
        (positiveTripleLaw security root scalar).weight word := by
  have hpoint (compensator : Palette security) :
      (positiveFourLaw security 0 root scalar).weight (Fin.cons compensator word) =
        (compensatorAt security 0).weight compensator * (positiveTripleLaw security root scalar).weight word := by
    change (((compensatorAt security 0).prod (positiveTripleLaw security root scalar)).map
      (consEquiv (Palette security))).weight (Fin.cons compensator word) = _
    rw [FiniteDist.map_equiv_weight]
    rfl
  simp only [hpoint, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
open _root_.P2M9e1cfc64 renaming h259 → _p2mH259
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h258 (security bits : ℕ) (root : ℤ) (scalar : FirstHistogram.Scalar security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (word : Fin 3 → Palette security) :
    |(fixed security bits root scalar.val (fun index => (word index).val) : ℝ) -
      (positiveTripleLaw security root scalar).weight word| ≤
      (Parameters.modulus security : ℝ) * RationalPositiveReferenceProgram.fixedErrorConstant security * (1 / (2 : ℝ)^bits) := by
  unfold fixed
  rw [PublicParameterProgram.modulus_value, Rat.cast_sum, ← _p2mH259, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _compensator : Palette security,
        RationalPositiveReferenceProgram.fixedErrorConstant security * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro compensator _
      exact _p2mH370 security bits 0 root scalar hprecision hbudget (Fin.cons compensator word)
    _ = _ := by simp; ring
open _root_.P2M9e1cfc64 renaming h258 → _p2mH258
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h251 (security : ℕ) : 0 ≤ atRootErrorConstant security := by
  unfold atRootErrorConstant RationalPositiveReferenceProgram.fixedErrorConstant RationalRootMassProgram.primaryErrorConstant
  positivity
open _root_.P2M9e1cfc64 renaming h251 → _p2mH251
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h252 (security bits : ℕ) (root : ℤ) (word : Fin 3 → Palette security) :
    (atRoot security bits root (fun index => (word index).val) : ℝ) =
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits).expectation
        (fun scalar => (fixed security bits root scalar.val (fun index => (word index).val) : ℝ)) := by
  have hcut : (security + 2)^2 - 1 = Parameters.sourceCutoff security - 1 := by
    simp only [Parameters.sourceCutoff, Parameters.base]
  rw [_p2mH253, hcut]
  simp only [Rat.cast_sum, Rat.cast_mul, RationalProposalProgram.gaussianWeight_eq,
    FiniteDist.expectation, windowApproxLaw]
open _root_.P2M9e1cfc64 renaming h252 → _p2mH252
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h254 (security bits : ℕ) (root : ℤ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (word : Fin 3 → Palette security) :
    |(atRoot security bits root (fun index => (word index).val) : ℝ) - (ActualBlockFock.primaryLawAt security root).weight word| ≤
      atRootErrorConstant security * (1 / (2 : ℝ)^bits) := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits
  let test := fun scalar : FirstHistogram.Scalar security => (positiveTripleLaw security root scalar).weight word
  let computed := fun scalar : FirstHistogram.Scalar security =>
    (fixed security bits root scalar.val (fun index => (word index).val) : ℝ)
  have hl1 : (∑ scalar, |approximate.weight scalar - (scalarLaw security).weight scalar|) ≤ 1 / (2 : ℝ)^bits :=
    _p2mH14 _ _ _ _ (_p2mH549 security)
      (_p2mH550 security).symm
  have htest (scalar : FirstHistogram.Scalar security) : |test scalar| ≤ 1 := by
    rw [abs_of_nonneg ((positiveTripleLaw security root scalar).nonneg word)]
    exact (positiveTripleLaw security root scalar).atom_le_one word
  have hk : |approximate.expectation computed - approximate.expectation test| ≤
      (Parameters.modulus security : ℝ) * RationalPositiveReferenceProgram.fixedErrorConstant security * (1 / (2 : ℝ)^bits) := by
    have h := _p2mH48 approximate (fun scalar => computed scalar - test scalar) _
      (fun scalar => _p2mH258 security bits root scalar hprecision hbudget word)
    simpa only [FiniteDist.expectation, mul_sub, Finset.sum_sub_distrib] using h
  have hs := (_p2mH70 approximate (scalarLaw security) test 1 htest).trans
    (by simpa only [one_mul] using hl1)
  rw [_p2mH252]
  rw [ActualBlockFock.primaryLawAt, FiniteDist.mix_weight]
  change |approximate.expectation computed - (scalarLaw security).expectation test| ≤ _
  exact (abs_sub_le _ (approximate.expectation test) _).trans ((add_le_add hk hs).trans_eq (by unfold atRootErrorConstant; ring))
open _root_.P2M9e1cfc64 renaming h254 → _p2mH254
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h257 (modulus : ℕ) [NeZero modulus] (color : Fin modulus) :
    ((ZMod.finEquiv modulus) color).val = color.val := by
  cases modulus with
  | zero => exact (NeZero.ne (0 : ℕ) rfl).elim
  | succ modulus => rfl
open _root_.P2M9e1cfc64 renaming h257 → _p2mH257
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h260 (security bits : ℕ) (word : Fin 3 → Palette security) :
    (mean security bits (fun index => (word index).val) : ℝ) =
      ∑ root : Root security, (RootSignedMassProgram.referenceEntry security bits root.val : ℝ) *
        (atRoot security bits root.val (fun index => (word index).val) : ℝ) := by
  unfold mean
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul]
  calc
    _ = ∑ root : Palette security,
        (RootSignedMassProgram.referenceEntry security bits ((ZMod.finEquiv (Parameters.modulus security)) root).val : ℝ) *
          (atRoot security bits ((ZMod.finEquiv (Parameters.modulus security)) root).val (fun index => (word index).val) : ℝ) := by
      apply Finset.sum_congr (by ext; simp)
      intro root _
      simp only [_p2mH257]
    _ = _ := (ZMod.finEquiv (Parameters.modulus security)).toEquiv.sum_comp (fun root : Root security =>
        (RootSignedMassProgram.referenceEntry security bits root.val : ℝ) *
          (atRoot security bits root.val (fun index => (word index).val) : ℝ))
open _root_.P2M9e1cfc64 renaming h260 → _p2mH260
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h261 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (word : Fin 3 → Palette security) :
    |(mean security bits (fun index => (word index).val) : ℝ) - RootTaggedLegHigher.rawMassLinear security 1 word| ≤
      meanErrorConstant security * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH260]
  simp only [RootTaggedLegHigher.rawMassLinear, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, mul_one]
  change |(∑ root : Root security, _) - ∑ root : Root security,
    (rootReference security).weight root * (ActualBlockFock.primaryLawAt security root.val).weight word| ≤ _
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _root : Root security, (atRootErrorConstant security + 2) * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro root _
      have hroot := _p2mH520 security bits root
      have hrootError := _p2mH522 security bits root
      have hvalue := _p2mH254 security bits root.val hprecision hbudget word
      have hmass : |(ActualBlockFock.primaryLawAt security root.val).weight word| ≤ 1 := by
        rw [abs_of_nonneg ((ActualBlockFock.primaryLawAt security root.val).nonneg word)]
        exact (ActualBlockFock.primaryLawAt security root.val).atom_le_one word
      calc
        _ = |(RootSignedMassProgram.referenceEntry security bits root.val : ℝ) *
            ((atRoot security bits root.val (fun index => (word index).val) : ℝ) - (ActualBlockFock.primaryLawAt security root.val).weight word) +
            ((RootSignedMassProgram.referenceEntry security bits root.val : ℝ) - (rootReference security).weight root) *
              (ActualBlockFock.primaryLawAt security root.val).weight word| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ 1 * (atRootErrorConstant security * (1 / (2 : ℝ)^bits)) + (2 / (2 : ℝ)^bits) * 1 := by
          simp only [abs_mul]
          exact add_le_add (mul_le_mul (by rw [abs_of_nonneg hroot.1]; exact hroot.2) hvalue (abs_nonneg _) (by norm_num))
            (mul_le_mul hrootError hmass (abs_nonneg _) (by positivity))
        _ = _ := by ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; unfold meanErrorConstant; ring
open _root_.P2M9e1cfc64 renaming h261 → _p2mH261
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h256 (security : ℕ) :
    0 ≤ meanErrorConstant security ∧ 0 ≤ differenceErrorConstant security := by
  have h := _p2mH251 security
  have hmean : 0 ≤ meanErrorConstant security := by unfold meanErrorConstant; positivity
  exact ⟨hmean, add_nonneg h hmean⟩
open _root_.P2M9e1cfc64 renaming h256 → _p2mH256
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h255 (security bits : ℕ) (root : ℤ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (word : Fin 3 → Palette security) :
    |(difference security bits root (fun index => (word index).val) : ℝ) -
      ((ActualBlockFock.primaryLawAt security root).weight word - RootTaggedLegHigher.rawMassLinear security 1 word)| ≤
      differenceErrorConstant security * (1 / (2 : ℝ)^bits) := by
  rw [difference, Rat.cast_sub]
  have hsplit : (atRoot security bits root (fun index => (word index).val) : ℝ) -
      (mean security bits (fun index => (word index).val) : ℝ) -
      ((ActualBlockFock.primaryLawAt security root).weight word - RootTaggedLegHigher.rawMassLinear security 1 word) =
      ((atRoot security bits root (fun index => (word index).val) : ℝ) - (ActualBlockFock.primaryLawAt security root).weight word) -
      ((mean security bits (fun index => (word index).val) : ℝ) - RootTaggedLegHigher.rawMassLinear security 1 word) := by ring
  rw [hsplit]
  exact (abs_sub _ _).trans ((add_le_add (_p2mH254 security bits root hprecision hbudget word)
    (_p2mH261 security bits hprecision hbudget word)).trans_eq (by unfold differenceErrorConstant; ring))
open _root_.P2M9e1cfc64 renaming h255 → _p2mH255
end
open _root_.P2M9e1cfc64 renaming h251 → _p2mH251
open _root_.P2M9e1cfc64 renaming h252 → _p2mH252
open _root_.P2M9e1cfc64 renaming h253 → _p2mH253
open _root_.P2M9e1cfc64 renaming h254 → _p2mH254
open _root_.P2M9e1cfc64 renaming h255 → _p2mH255
open _root_.P2M9e1cfc64 renaming h256 → _p2mH256
open _root_.P2M9e1cfc64 renaming h257 → _p2mH257
open _root_.P2M9e1cfc64 renaming h258 → _p2mH258
open _root_.P2M9e1cfc64 renaming h259 → _p2mH259
open _root_.P2M9e1cfc64 renaming h260 → _p2mH260
open _root_.P2M9e1cfc64 renaming h261 → _p2mH261
end CurrentAFT.RationalLegMassProgram
open _root_.P2M9e1cfc64 renaming h251 → _p2mH251
open _root_.P2M9e1cfc64 renaming h252 → _p2mH252
open _root_.P2M9e1cfc64 renaming h253 → _p2mH253
open _root_.P2M9e1cfc64 renaming h254 → _p2mH254
open _root_.P2M9e1cfc64 renaming h255 → _p2mH255
open _root_.P2M9e1cfc64 renaming h256 → _p2mH256
open _root_.P2M9e1cfc64 renaming h257 → _p2mH257
open _root_.P2M9e1cfc64 renaming h258 → _p2mH258
open _root_.P2M9e1cfc64 renaming h259 → _p2mH259
open _root_.P2M9e1cfc64 renaming h260 → _p2mH260
open _root_.P2M9e1cfc64 renaming h261 → _p2mH261
end
open _root_.P2M9e1cfc64 renaming h257 → _p2mH257
open _root_.P2M9e1cfc64 renaming h260 → _p2mH260
open _root_.P2M9e1cfc64 renaming h258 → _p2mH258
open _root_.P2M9e1cfc64 renaming h254 → _p2mH254
open _root_.P2M9e1cfc64 renaming h251 → _p2mH251
open _root_.P2M9e1cfc64 renaming h252 → _p2mH252
open _root_.P2M9e1cfc64 renaming h256 → _p2mH256
open _root_.P2M9e1cfc64 renaming h253 → _p2mH253
open _root_.P2M9e1cfc64 renaming h259 → _p2mH259
open _root_.P2M9e1cfc64 renaming h255 → _p2mH255
open _root_.P2M9e1cfc64 renaming h261 → _p2mH261
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
theorem _root_.P2M9e1cfc64.h182 (r s : ℕ) (value : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℚ) :
    ((average r s value : ℚ) : ℝ) = average r s (fun first second => (value first second : ℝ)) := by
  simp only [average, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum]
open _root_.P2M9e1cfc64 renaming h182 → _p2mH182
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h188 {Primary Body : Type*} {r s r' s' : ℕ}
    (first : Kernel ℚ Primary Body r s) (second : Kernel ℚ Primary Body r' s')
    (colors : Fin (r+r') → Primary) (centers : Fin (s+s') → Body) :
    ((homogeneous first second colors centers : ℚ) : ℝ) =
      homogeneous (fun colors centers => (first colors centers : ℝ))
        (fun colors centers => (second colors centers : ℝ)) colors centers := by
  rw [homogeneous, _p2mH182]
  simp only [tensor, Rat.cast_mul, homogeneous]
open _root_.P2M9e1cfc64 renaming h188 → _p2mH188
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h197 {Primary Body : Type*} (order : ℕ) (first second : Table ℚ Primary Body order) :
    realTable order (product order first second) = product order (realTable order first) (realTable order second) := by
  funext output colors centers
  simp only [realTable, product, Rat.cast_sum]
  apply Finset.sum_congr (by ext left; simp)
  intro left _
  apply Finset.sum_congr (by ext right; simp)
  intro right _
  split_ifs with hmatch
  · exact _p2mH188 (first left) (second right) _ _
  · exact Rat.cast_zero
open _root_.P2M9e1cfc64 renaming h197 → _p2mH197
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h186 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) {r s r' s' : ℕ}
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s') :
    homogeneous first.val second.val = (homogeneousProduct primary body first second).val := by
  funext colors centers
  rw [_p2mH52]
  unfold homogeneous average
  apply congrArg (fun total : ℝ => ((r+r').factorial : ℝ)⁻¹ * ((s+s').factorial : ℝ)⁻¹ * total)
  apply Finset.sum_congr (by ext first; simp)
  intro firstOrder _
  apply Finset.sum_congr (by ext second; simp)
  intro secondOrder _
  rfl
open _root_.P2M9e1cfc64 renaming h186 → _p2mH186
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h195 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order) :
    product order (fun arity => (first arity).val) (fun arity => (second arity).val) =
      fun arity => (familyProduct primary body order first second arity).val := by
  funext output colors centers
  simp only [product, familyProduct, Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr (by ext left; simp)
  intro left _
  apply Finset.sum_congr (by ext right; simp)
  intro right _
  split_ifs with hmatch
  · rw [_p2mH186, transportKernel_val]
    rfl
  · rfl
open _root_.P2M9e1cfc64 renaming h195 → _p2mH195
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h181 (r s : ℕ)
    (value : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℝ) (bound : ℝ)
    (hvalue : ∀ first second, |value first second| ≤ bound) : |average r s value| ≤ bound := by
  have h := _p2mH48
    ((FiniteDist.uniform (Equiv.Perm (Fin r))).prod (FiniteDist.uniform (Equiv.Perm (Fin s))))
    (fun pair => value pair.1 pair.2) bound (fun pair => hvalue pair.1 pair.2)
  convert h using 1
  congr 1
  simp only [average, FiniteDist.expectation, FiniteDist.prod_weight, FiniteDist.uniform_weight,
    Fintype.sum_prod_type, Fintype.card_perm, Fintype.card_fin, ← Finset.mul_sum]
  apply congrArg (fun total : ℝ => (r.factorial : ℝ)⁻¹ * (s.factorial : ℝ)⁻¹ * total)
  apply Finset.sum_congr (by ext first; simp)
  intro first _
  apply Finset.sum_congr (by ext second; simp)
  intro second _
  rfl
open _root_.P2M9e1cfc64 renaming h181 → _p2mH181
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h183 (r s : ℕ) (first second : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℝ) :
    average r s first - average r s second = average r s (fun p b => first p b - second p b) := by
  simp only [average, Finset.sum_sub_distrib, mul_sub]
open _root_.P2M9e1cfc64 renaming h183 → _p2mH183
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h190 (first second computedFirst computedSecond A B e f : ℝ)
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
open _root_.P2M9e1cfc64 renaming h190 → _p2mH190
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h187 {Primary Body : Type*} {r s r' s' : ℕ}
    (first : Kernel ℝ Primary Body r s) (second : Kernel ℝ Primary Body r' s')
    (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (ha : ∀ colors centers, |first colors centers| ≤ A)
    (hb : ∀ colors centers, |second colors centers| ≤ B)
    (colors : Fin (r+r') → Primary) (centers : Fin (s+s') → Body) :
    |homogeneous first second colors centers| ≤ A*B := by
  apply _p2mH181
  intro p b
  unfold tensor
  rw [abs_mul]
  exact mul_le_mul (ha _ _) (hb _ _) (abs_nonneg _) hA
open _root_.P2M9e1cfc64 renaming h187 → _p2mH187
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h189 {Primary Body : Type*} {r s r' s' : ℕ}
    (first computedFirst : Kernel ℝ Primary Body r s) (second computedSecond : Kernel ℝ Primary Body r' s')
    (A B e f : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hf : 0 ≤ f)
    (ha : ∀ colors centers, |first colors centers| ≤ A)
    (hb : ∀ colors centers, |second colors centers| ≤ B)
    (hea : ∀ colors centers, |computedFirst colors centers-first colors centers| ≤ e)
    (heb : ∀ colors centers, |computedSecond colors centers-second colors centers| ≤ f)
    (colors : Fin (r+r') → Primary) (centers : Fin (s+s') → Body) :
    |homogeneous computedFirst computedSecond colors centers - homogeneous first second colors centers| ≤
      e*B + (A+e)*f := by
  unfold homogeneous
  rw [_p2mH183]
  apply _p2mH181
  intro p b
  exact _p2mH190 _ _ _ _ A B e f hA hB he hf (ha _ _) (hb _ _) (hea _ _) (heb _ _)
open _root_.P2M9e1cfc64 renaming h189 → _p2mH189
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h198 {Primary Body : Type*} (order : ℕ)
    (first computedFirst second computedSecond : Table ℝ Primary Body order)
    (A B e f : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hf : 0 ≤ f)
    (ha : ∀ arity colors centers, |first arity colors centers| ≤ A)
    (hb : ∀ arity colors centers, |second arity colors centers| ≤ B)
    (hea : ∀ arity colors centers, |computedFirst arity colors centers-first arity colors centers| ≤ e)
    (heb : ∀ arity colors centers, |computedSecond arity colors centers-second arity colors centers| ≤ f)
    (output : TruncatedArity order) (colors : Fin output.val.1.val → Primary)
    (centers : Fin output.val.2.val → Body) :
    |product order computedFirst computedSecond output colors centers - product order first second output colors centers| ≤
      (Fintype.card (TruncatedArity order) : ℝ)^2 * (e*B + (A+e)*f) := by
  unfold product
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _left : TruncatedArity order, ∑ _right : TruncatedArity order, (e*B + (A+e)*f) := by
      apply Finset.sum_le_sum
      intro left _
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro right _
      split_ifs with hmatch
      · exact _p2mH189 _ _ _ _ A B e f hA hB he hf (ha left) (hb right) (hea left) (heb right) _ _
      · simp only [sub_self, abs_zero]
        positivity
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
open _root_.P2M9e1cfc64 renaming h198 → _p2mH198
end
open _root_.P2M9e1cfc64 renaming h181 → _p2mH181
open _root_.P2M9e1cfc64 renaming h182 → _p2mH182
open _root_.P2M9e1cfc64 renaming h183 → _p2mH183
open _root_.P2M9e1cfc64 renaming h186 → _p2mH186
open _root_.P2M9e1cfc64 renaming h187 → _p2mH187
open _root_.P2M9e1cfc64 renaming h188 → _p2mH188
open _root_.P2M9e1cfc64 renaming h189 → _p2mH189
open _root_.P2M9e1cfc64 renaming h190 → _p2mH190
open _root_.P2M9e1cfc64 renaming h195 → _p2mH195
open _root_.P2M9e1cfc64 renaming h197 → _p2mH197
open _root_.P2M9e1cfc64 renaming h198 → _p2mH198
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M9e1cfc64 renaming h181 → _p2mH181
open _root_.P2M9e1cfc64 renaming h182 → _p2mH182
open _root_.P2M9e1cfc64 renaming h183 → _p2mH183
open _root_.P2M9e1cfc64 renaming h186 → _p2mH186
open _root_.P2M9e1cfc64 renaming h187 → _p2mH187
open _root_.P2M9e1cfc64 renaming h188 → _p2mH188
open _root_.P2M9e1cfc64 renaming h189 → _p2mH189
open _root_.P2M9e1cfc64 renaming h190 → _p2mH190
open _root_.P2M9e1cfc64 renaming h195 → _p2mH195
open _root_.P2M9e1cfc64 renaming h197 → _p2mH197
open _root_.P2M9e1cfc64 renaming h198 → _p2mH198
end
open _root_.P2M9e1cfc64 renaming h181 → _p2mH181
open _root_.P2M9e1cfc64 renaming h190 → _p2mH190
open _root_.P2M9e1cfc64 renaming h188 → _p2mH188
open _root_.P2M9e1cfc64 renaming h189 → _p2mH189
open _root_.P2M9e1cfc64 renaming h182 → _p2mH182
open _root_.P2M9e1cfc64 renaming h197 → _p2mH197
open _root_.P2M9e1cfc64 renaming h195 → _p2mH195
open _root_.P2M9e1cfc64 renaming h186 → _p2mH186
open _root_.P2M9e1cfc64 renaming h187 → _p2mH187
open _root_.P2M9e1cfc64 renaming h198 → _p2mH198
open _root_.P2M9e1cfc64 renaming h183 → _p2mH183
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT RationalNumerics GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h196 {Primary Body : Type*} (order : ℕ)
    (first second : Table ℝ Primary Body order) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ arity colors centers, |first arity colors centers| ≤ A)
    (hb : ∀ arity colors centers, |second arity colors centers| ≤ B)
    (output : TruncatedArity order) (colors : Fin output.val.1.val → Primary)
    (centers : Fin output.val.2.val → Body) :
    |product order first second output colors centers| ≤
      (Fintype.card (TruncatedArity order) : ℝ)^2 * (A*B) := by
  unfold product
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _left : TruncatedArity order, ∑ _right : TruncatedArity order, (A*B) := by
      apply Finset.sum_le_sum
      intro left _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro right _
      split_ifs with hmatch
      · exact _p2mH187 _ _ A B hA hB (ha left) (hb right) _ _
      · simpa only [abs_zero] using mul_nonneg hA hB
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
open _root_.P2M9e1cfc64 renaming h196 → _p2mH196
end
open _root_.P2M9e1cfc64 renaming h196 → _p2mH196
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M9e1cfc64 renaming h196 → _p2mH196
end
open _root_.P2M9e1cfc64 renaming h196 → _p2mH196
namespace CurrentAFT.RationalFamilyProductProgram
end CurrentAFT.RationalFamilyProductProgram
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
theorem _root_.P2M9e1cfc64.h210 {Primary Body : Type*} (order : ℕ) :
    realTable order (unit (Scalar := ℚ) (Primary := Primary) (Body := Body) order) = unit order := by
  funext arity colors centers
  simp only [realTable, unit, apply_ite, Rat.cast_one, Rat.cast_zero]
  split_ifs <;> rfl
open _root_.P2M9e1cfc64 renaming h210 → _p2mH210
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h193 {Primary Body : Type*} (order : ℕ) (table : Table ℚ Primary Body order) (count : ℕ) :
    realTable order (power order table count) = power order (realTable order table) count := by
  induction count with
  | zero => exact _p2mH210 order
  | succ count ih => simp only [power, _p2mH197, ih]
open _root_.P2M9e1cfc64 renaming h193 → _p2mH193
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h206 {Primary Body : Type*} (order : ℕ) (table : Table ℚ Primary Body order) :
    realTable order (reciprocal order table) = reciprocal order (realTable order table) := by
  have hsub : realTable order (unit order - table) = unit order - realTable order table := by
    funext arity colors centers
    simp only [realTable, Pi.sub_apply, Rat.cast_sub]
    exact congrArg (fun value => value - (table arity colors centers : ℝ))
      (congrFun (congrFun (congrFun (_p2mH210 (Primary := Primary) (Body := Body) order) arity) colors) centers)
  funext arity colors centers
  simp only [realTable, reciprocal, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro count _
  change realTable order (power order (unit order - table) count) arity colors centers = _
  rw [_p2mH193, hsub]
open _root_.P2M9e1cfc64 renaming h206 → _p2mH206
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h208 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    unit (Scalar := ℝ) (Primary := Primary) (Body := Body) order =
      fun arity => ((1 : KernelFamily primary body order) arity).val := by
  funext arity colors centers
  unfold unit
  change _ = ((familyUnit primary body order) arity).val colors centers
  by_cases heq : arity = zeroArity order
  · subst arity
    simp only [familyUnit, Pi.single_eq_same, if_true, scalarUnit]
  · simp only [familyUnit, Pi.single_eq_of_ne heq, heq, if_false, Submodule.coe_zero, Pi.zero_apply]
open _root_.P2M9e1cfc64 renaming h208 → _p2mH208
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h191 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order count : ℕ)
    (family : KernelFamily primary body order) :
    power order (fun arity => (family arity).val) count = fun arity => ((family^count) arity).val := by
  induction count with
  | zero => exact _p2mH208 primary body order
  | succ count ih =>
      rw [power, ih, _p2mH195, pow_succ]
      rfl
open _root_.P2M9e1cfc64 renaming h191 → _p2mH191
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h204 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) :
    reciprocal order (fun arity => (family arity).val) =
      fun arity => (backgroundInverse primary body order family arity).val := by
  have hsub : unit order - (fun arity => (family arity).val) =
      fun arity => ((1 - family : KernelFamily primary body order) arity).val := by
    rw [_p2mH208 primary body order]
    rfl
  funext arity colors centers
  simp only [reciprocal, hsub, _p2mH191, backgroundInverse, Finset.sum_apply, Submodule.coe_sum]
open _root_.P2M9e1cfc64 renaming h204 → _p2mH204
end
open _root_.P2M9e1cfc64 renaming h191 → _p2mH191
open _root_.P2M9e1cfc64 renaming h193 → _p2mH193
open _root_.P2M9e1cfc64 renaming h204 → _p2mH204
open _root_.P2M9e1cfc64 renaming h206 → _p2mH206
open _root_.P2M9e1cfc64 renaming h208 → _p2mH208
open _root_.P2M9e1cfc64 renaming h210 → _p2mH210
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M9e1cfc64 renaming h191 → _p2mH191
open _root_.P2M9e1cfc64 renaming h193 → _p2mH193
open _root_.P2M9e1cfc64 renaming h204 → _p2mH204
open _root_.P2M9e1cfc64 renaming h206 → _p2mH206
open _root_.P2M9e1cfc64 renaming h208 → _p2mH208
open _root_.P2M9e1cfc64 renaming h210 → _p2mH210
end
open _root_.P2M9e1cfc64 renaming h208 → _p2mH208
open _root_.P2M9e1cfc64 renaming h191 → _p2mH191
open _root_.P2M9e1cfc64 renaming h206 → _p2mH206
open _root_.P2M9e1cfc64 renaming h210 → _p2mH210
open _root_.P2M9e1cfc64 renaming h193 → _p2mH193
open _root_.P2M9e1cfc64 renaming h204 → _p2mH204
section
namespace CurrentAFT.RationalLegFamilyTable
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalLegFamilyTable.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalLegFamilyTable.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h246 (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    insertSelected order selected
      (fun word => (RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val word Fin.elim0)
        arity colors centers =
      (RootLegCoefficientFamily.selectedFamily security order mass selected arity).val colors centers := by
  unfold insertSelected RootLegCoefficientFamily.selectedFamily
  by_cases hdegree : selected.card ≤ order
  · rw [dif_pos hdegree]
    by_cases hmatch : selected.card = arity.val.1.val ∧ 0 = arity.val.2.val
    · have harity : arity = RootLegCoefficientFamily.selectedArity order selected hdegree := by
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          exact hmatch.1.symm
        · apply Fin.ext
          exact hmatch.2.symm
      subst arity
      rw [dif_pos hmatch, Pi.single_eq_same]
      have hcenters : centers = (Fin.elim0 : Fin 0 → SafePalette security) :=
        @Subsingleton.elim (Fin 0 → SafePalette security) inferInstance centers Fin.elim0
      rw [hcenters]
      rfl
    · have harity : arity ≠ RootLegCoefficientFamily.selectedArity order selected hdegree := by
        intro hequal
        apply hmatch
        subst arity
        exact ⟨rfl, rfl⟩
      rw [dif_neg hmatch]
      have hzero := Pi.single_eq_of_ne
        (M := fun point : TruncatedArity order =>
          canonicalKernels (primaryLaw security) (bodyReference security) point.val.1.val point.val.2.val) harity
        (RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp))
      rw [hzero]
      rfl
  · rw [dif_neg hdegree]
    have hmatch : ¬(selected.card = arity.val.1.val ∧ 0 = arity.val.2.val) := by
      intro h
      have hbound := arity.property
      omega
    rw [dif_neg hmatch]
    rfl
open _root_.P2M9e1cfc64 renaming h246 → _p2mH246
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h247 (order : ℕ) (selected : Finset (Fin 3)) (security : ℕ)
    (computed : (Fin selected.card → ℕ) → ℚ) (actual : (Fin selected.card → Palette security) → ℝ)
    (error : ℝ) (he : 0 ≤ error)
    (hvalue : ∀ word, |(computed (fun index => (word index).val) : ℝ) - actual word| ≤ error)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(insertSelected order selected computed arity (fun index => (colors index).val)
        (fun index => (centers index).val.val) : ℝ) -
      insertSelected order selected actual arity colors centers| ≤ error := by
  unfold insertSelected
  split_ifs with hmatch
  · exact hvalue (colors ∘ finCongr hmatch.1)
  · simpa only [Rat.cast_zero, sub_self, abs_zero] using he
open _root_.P2M9e1cfc64 renaming h247 → _p2mH247
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h248 (security degree : ℕ) (massBound massError : ℝ)
    (hbound : 0 ≤ massBound) (herror : 0 ≤ massError) :
    0 ≤ RationalLegCoefficientExtraction.normalizedError security degree massBound massError := by
  unfold RationalLegCoefficientExtraction.normalizedError RationalLegCoefficientExtraction.extractionBound
    RationalLegCoefficientExtraction.extractionError RationalLegCoefficientExtraction.atomErrorConstant
    RationalTensorInverseProgram.tensorErrorConstant RationalRootMassProgram.primaryErrorConstant
  positivity [_p2mH455 security,
    _p2mH462 security, _p2mH463 security]
open _root_.P2M9e1cfc64 renaming h248 → _p2mH248
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h245 (security bits order : ℕ) (computed : (Fin 3 → ℕ) → ℚ)
    (mass : (Fin 3 → Palette security) → ℝ) (massBound massError : ℝ)
    (hbound : 0 ≤ massBound) (herror : 0 ≤ massError)
    (hmass : ∀ word, |mass word| ≤ massBound)
    (hdiff : ∀ word : Fin 3 → Palette security,
      |(computed (fun index => (word index).val) : ℝ) - mass word| ≤ massError * (1 / (2 : ℝ)^bits))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(higher security bits order computed arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootLegCoefficientLinear.higherFamilyLinear security order mass arity).val colors centers| ≤
      higherError security massBound massError * (1 / (2 : ℝ)^bits) := by
  have hsum : (higher security bits order computed arity
      (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card),
        (insertSelected order selected (RationalLegCoefficientExtraction.selectedKernel security bits computed selected)
          arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) := by
    unfold higher
    simp only [Rat.cast_sum]
  rw [hsum, RootLegCoefficientLinear.higherFamilyLinear_apply]
  simp only [RootLegCoefficientFamily.higherFamily, Finset.sum_apply, Submodule.coe_sum]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card),
        RationalLegCoefficientExtraction.normalizedError security selected.card massBound massError * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro selected _
      rw [← _p2mH246 security order mass selected arity colors centers]
      exact _p2mH247 order selected security _ _ _
        (by positivity [_p2mH248 security selected.card massBound massError hbound herror])
        (fun word => _p2mH242 security bits computed mass selected massBound massError
          hbound herror hmass hdiff hfirst hprecision hbudget word Fin.elim0) arity colors centers
    _ = _ := by unfold higherError; rw [Finset.sum_mul]
open _root_.P2M9e1cfc64 renaming h245 → _p2mH245
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h249 (security order : ℕ) (law : FiniteDist (Fin 3 → Palette security))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    (RootLegNormalized.positiveFamily security order law arity).val colors centers =
      RationalFamilyProductProgram.unit order arity colors centers +
        ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
          insertSelected order selected
            (fun word => (RootLegCoefficientFamily.selectedKernel security selected.card law.weight selected (by simp)).val word Fin.elim0)
            arity colors centers := by
  unfold RootLegNormalized.positiveFamily RootLegNormalized.completeFamily
  rw [FiniteDist.sum_one, one_smul]
  simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_apply, Submodule.coe_sum]
  have hunit := congrFun (congrFun (congrFun
    (_p2mH208 (primaryLaw security) (bodyReference security) order) arity) colors) centers
  rw [← hunit]
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro selected _
  exact (_p2mH246 security order law.weight selected arity colors centers).symm
open _root_.P2M9e1cfc64 renaming h249 → _p2mH249
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h250 (security bits order : ℕ) (computed : (Fin 3 → ℕ) → ℚ)
    (law : FiniteDist (Fin 3 → Palette security)) (massError : ℝ) (herror : 0 ≤ massError)
    (hdiff : ∀ word : Fin 3 → Palette security,
      |(computed (fun index => (word index).val) : ℝ) - law.weight word| ≤ massError * (1 / (2 : ℝ)^bits))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(positive security bits order computed arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootLegNormalized.positiveFamily security order law arity).val colors centers| ≤
      positiveError security massError * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH249]
  have hcast : (positive security bits order computed arity
      (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) =
      RationalFamilyProductProgram.unit order arity colors centers +
        ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
          (insertSelected order selected (RationalLegCoefficientExtraction.selectedKernel security bits computed selected)
            arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) := by
    simp only [positive, Rat.cast_add, Rat.cast_sum]
    congr 1
    unfold RationalFamilyProductProgram.unit
    split_ifs <;> norm_num
  rw [hcast, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
        RationalLegCoefficientExtraction.normalizedError security selected.card 1 massError * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro selected _
      exact _p2mH247 order selected security _ _ _
        (by positivity [_p2mH248 security selected.card 1 massError (by norm_num) herror])
        (fun word => _p2mH242 security bits computed law.weight selected 1 massError
          (by norm_num) herror (fun word => by rw [abs_of_nonneg (law.nonneg word)]; exact law.atom_le_one word)
          hdiff hfirst hprecision hbudget word Fin.elim0) arity colors centers
    _ = _ := by unfold positiveError; rw [Finset.sum_mul]
open _root_.P2M9e1cfc64 renaming h250 → _p2mH250
end
open _root_.P2M9e1cfc64 renaming h245 → _p2mH245
open _root_.P2M9e1cfc64 renaming h246 → _p2mH246
open _root_.P2M9e1cfc64 renaming h247 → _p2mH247
open _root_.P2M9e1cfc64 renaming h248 → _p2mH248
open _root_.P2M9e1cfc64 renaming h249 → _p2mH249
open _root_.P2M9e1cfc64 renaming h250 → _p2mH250
end CurrentAFT.RationalLegFamilyTable
open _root_.P2M9e1cfc64 renaming h245 → _p2mH245
open _root_.P2M9e1cfc64 renaming h246 → _p2mH246
open _root_.P2M9e1cfc64 renaming h247 → _p2mH247
open _root_.P2M9e1cfc64 renaming h248 → _p2mH248
open _root_.P2M9e1cfc64 renaming h249 → _p2mH249
open _root_.P2M9e1cfc64 renaming h250 → _p2mH250
end
open _root_.P2M9e1cfc64 renaming h245 → _p2mH245
open _root_.P2M9e1cfc64 renaming h248 → _p2mH248
open _root_.P2M9e1cfc64 renaming h249 → _p2mH249
open _root_.P2M9e1cfc64 renaming h246 → _p2mH246
open _root_.P2M9e1cfc64 renaming h247 → _p2mH247
open _root_.P2M9e1cfc64 renaming h250 → _p2mH250
section
namespace CurrentAFT.LegCoefficientPointBounds
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.LegCoefficientPointBounds.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.LegCoefficientPointBounds.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h99 (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → Palette security) :
    |RationalLegCoefficientExtraction.orderedDensity security mass selected output| ≤
      (Parameters.modulus security : ℝ)^3 * bound * (4 * (Parameters.modulus security : ℝ))^selected.card := by
  unfold RationalLegCoefficientExtraction.orderedDensity LocalTensors.referenceRestrictedComponent
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _word : Fin 3 → Palette security, bound * (4 * (Parameters.modulus security : ℝ))^selected.card := by
      apply Finset.sum_le_sum
      intro word _
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul (hmass word) _ (Finset.prod_nonneg fun _ _ => abs_nonneg _) hb
      calc
        _ ≤ ∏ _slot : selected, 4 * (Parameters.modulus security : ℝ) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun slot _ => _p2mH229 security _ _)
        _ = _ := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
open _root_.P2M9e1cfc64 renaming h99 → _p2mH99
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h105 (security degree : ℕ) (profile : (Fin degree → Palette security) → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hprofile : ∀ word, |profile word| ≤ bound)
    (output : Fin degree → Palette security) :
    |PrimaryTensorInverse.tensorInverse security degree profile output| ≤
      (Parameters.modulus security : ℝ)^degree * (RationalTensorInverseProgram.actualBound security)^degree * bound := by
  have h := _p2mH457 security degree profile 0 bound hb
    (fun word => by simpa only [Pi.zero_apply, sub_zero] using hprofile word) output
  simpa only [map_zero, Pi.zero_apply, sub_zero] using h
open _root_.P2M9e1cfc64 renaming h105 → _p2mH105
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h102 (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → Palette security) (centers : Fin 0 → SafePalette security) :
    |(RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output centers| ≤
      (Parameters.modulus security : ℝ)^selected.card * (RationalTensorInverseProgram.actualBound security)^selected.card *
        ((Parameters.modulus security : ℝ)^3 * bound * (4 * (Parameters.modulus security : ℝ))^selected.card) := by
  rw [_p2mH230]
  apply _p2mH48
  intro permutation
  exact _p2mH105 security selected.card _ _ (by positivity) (_p2mH99 security mass selected bound hb hmass)
    (output ∘ permutation)
open _root_.P2M9e1cfc64 renaming h102 → _p2mH102
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h101 (security : ℕ) (bound : ℝ) (hb : 0 ≤ bound) : 0 ≤ selectedBound security bound := by
  unfold selectedBound
  positivity [_p2mH455 security]
open _root_.P2M9e1cfc64 renaming h101 → _p2mH101
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h103 (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → Palette security) (centers : Fin 0 → SafePalette security) :
    |(RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output centers| ≤
      selectedBound security bound := by
  have hcard : selected.card ≤ 3 := (Finset.card_le_card (Finset.subset_univ selected)).trans_eq (by simp)
  have hq : (1 : ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_spec security).2.two_le.trans' (by omega)
  have hM := _p2mH455 security
  have hqpow := pow_le_pow_right₀ hq hcard
  have hfour : (1 : ℝ) ≤ 4 * (Parameters.modulus security : ℝ) := by linarith
  have hfourpow := pow_le_pow_right₀ hfour hcard
  have hMpow : (RationalTensorInverseProgram.actualBound security)^selected.card ≤
      (1 + RationalTensorInverseProgram.actualBound security)^3 :=
    (pow_le_pow_left₀ hM (show RationalTensorInverseProgram.actualBound security ≤
        1 + RationalTensorInverseProgram.actualBound security by linarith) selected.card).trans
      (pow_le_pow_right₀ (by linarith) hcard)
  apply (_p2mH102 security mass selected bound hb hmass output centers).trans
  exact mul_le_mul (mul_le_mul hqpow hMpow (pow_nonneg hM _) (by positivity))
    (mul_le_mul_of_nonneg_left hfourpow (by positivity)) (by positivity) (by positivity)
open _root_.P2M9e1cfc64 renaming h103 → _p2mH103
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h98 (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootLegCoefficientFamily.selectedFamily security order mass selected arity).val colors centers| ≤ selectedBound security bound := by
  rw [← _p2mH246 security order mass selected arity colors centers]
  unfold RationalLegFamilyTable.insertSelected
  split_ifs with hmatch
  · exact _p2mH103 security mass selected bound hb hmass (colors ∘ finCongr hmatch.1) Fin.elim0
  · simpa only [abs_zero] using _p2mH101 security bound hb
open _root_.P2M9e1cfc64 renaming h98 → _p2mH98
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h104 (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selectedSets : Finset (Finset (Fin 3))) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |∑ selected ∈ selectedSets, (RootLegCoefficientFamily.selectedFamily security order mass selected arity).val colors centers| ≤
      8 * selectedBound security bound := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _selected ∈ selectedSets, selectedBound security bound :=
      Finset.sum_le_sum (fun selected _ => _p2mH98 security order mass selected bound hb hmass arity colors centers)
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (_p2mH101 security bound hb)
      apply Nat.cast_le.mpr
      exact (Finset.card_le_card (Finset.subset_univ selectedSets)).trans_eq (by norm_num)
open _root_.P2M9e1cfc64 renaming h104 → _p2mH104
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h97 (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootLegCoefficientLinear.higherFamilyLinear security order mass arity).val colors centers| ≤
      8 * selectedBound security bound := by
  rw [RootLegCoefficientLinear.higherFamilyLinear_apply]
  simpa only [RootLegCoefficientFamily.higherFamily, Finset.sum_apply, Submodule.coe_sum] using
    _p2mH104 security order mass _ bound hb hmass arity colors centers
open _root_.P2M9e1cfc64 renaming h97 → _p2mH97
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h100 (security order : ℕ) (law : FiniteDist (Fin 3 → Palette security))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootLegNormalized.positiveFamily security order law arity).val colors centers| ≤
      1 + 8 * selectedBound security 1 := by
  unfold RootLegNormalized.positiveFamily RootLegNormalized.completeFamily
  rw [law.sum_one, one_smul]
  simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_apply, Submodule.coe_sum]
  have hu : |((1 : RootLegCoefficientFamily.Family security order) arity).val colors centers| ≤ 1 := by
    rw [← congrFun (congrFun (congrFun
      (_p2mH208 (primaryLaw security) (bodyReference security) order) arity) colors) centers]
    unfold RationalFamilyProductProgram.unit
    split_ifs <;> norm_num
  exact (abs_add_le _ _).trans (add_le_add hu (_p2mH104 security order law.weight _ 1 (by norm_num)
    (fun word => by rw [abs_of_nonneg (law.nonneg word)]; exact law.atom_le_one word) arity colors centers))
open _root_.P2M9e1cfc64 renaming h100 → _p2mH100
end
open _root_.P2M9e1cfc64 renaming h97 → _p2mH97
open _root_.P2M9e1cfc64 renaming h98 → _p2mH98
open _root_.P2M9e1cfc64 renaming h99 → _p2mH99
open _root_.P2M9e1cfc64 renaming h100 → _p2mH100
open _root_.P2M9e1cfc64 renaming h101 → _p2mH101
open _root_.P2M9e1cfc64 renaming h102 → _p2mH102
open _root_.P2M9e1cfc64 renaming h103 → _p2mH103
open _root_.P2M9e1cfc64 renaming h104 → _p2mH104
open _root_.P2M9e1cfc64 renaming h105 → _p2mH105
end CurrentAFT.LegCoefficientPointBounds
open _root_.P2M9e1cfc64 renaming h97 → _p2mH97
open _root_.P2M9e1cfc64 renaming h98 → _p2mH98
open _root_.P2M9e1cfc64 renaming h99 → _p2mH99
open _root_.P2M9e1cfc64 renaming h100 → _p2mH100
open _root_.P2M9e1cfc64 renaming h101 → _p2mH101
open _root_.P2M9e1cfc64 renaming h102 → _p2mH102
open _root_.P2M9e1cfc64 renaming h103 → _p2mH103
open _root_.P2M9e1cfc64 renaming h104 → _p2mH104
open _root_.P2M9e1cfc64 renaming h105 → _p2mH105
end
open _root_.P2M9e1cfc64 renaming h105 → _p2mH105
open _root_.P2M9e1cfc64 renaming h102 → _p2mH102
open _root_.P2M9e1cfc64 renaming h103 → _p2mH103
open _root_.P2M9e1cfc64 renaming h101 → _p2mH101
open _root_.P2M9e1cfc64 renaming h97 → _p2mH97
open _root_.P2M9e1cfc64 renaming h98 → _p2mH98
open _root_.P2M9e1cfc64 renaming h100 → _p2mH100
open _root_.P2M9e1cfc64 renaming h99 → _p2mH99
open _root_.P2M9e1cfc64 renaming h104 → _p2mH104
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
theorem _root_.P2M9e1cfc64.h270 (security : ℕ) (profile : Palette security → ℝ) (output : Palette security) :
    actual security profile output = (FirstResponse.responseEquiv security).symm profile output /
      (activation security * (primaryLaw security).weight output) := by
  change PrimaryTensorInverse.densityInverse security (RootTaggedLocal.profileDensity security profile) output = _
  rw [PrimaryTensorInverse.densityInverse_apply]
  have hprofile : (fun color => (primaryLaw security).weight color * RootTaggedLocal.profileDensity security profile color) = profile := by
    funext color
    rw [RootTaggedLocal.profileDensity_apply]
    field_simp [(primaryReference_positive security color).ne']
  rw [hprofile]
  ring
open _root_.P2M9e1cfc64 renaming h270 → _p2mH270
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h269 (security : ℕ) (output : Palette security) :
    1 / (8 * (Parameters.base security : ℝ) * Parameters.modulus security) ≤
      activation security * (primaryLaw security).weight output := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have hp : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
    simpa only [primaryLaw] using primaryProfile_atom_lower security output
  calc
    _ = (1 / (4 * (Parameters.base security : ℝ))) * (1 / (2 * (Parameters.modulus security : ℝ))) := by ring
    _ ≤ _ := mul_le_mul (FirstResponse.activation_lower_simple security) hp (by positivity) (activation_pos security).le
open _root_.P2M9e1cfc64 renaming h269 → _p2mH269
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h272 (security bits : ℕ) (output : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits) :
    1 / (32 * (Parameters.base security : ℝ) * Parameters.modulus security) ≤
      (LocalPairProgram.activationApprox security bits : ℝ) * (primary security bits output.val : ℝ) := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have ha := _p2mH176 security bits hfirst
  have hp := RationalProposalProgram.primary_lower security bits output
  calc
    _ = (1 / (8 * (Parameters.base security : ℝ))) * (1 / (4 * (Parameters.modulus security : ℝ))) := by ring
    _ ≤ _ := mul_le_mul ha hp (by positivity) (LocalPairProgram.activationApprox_bounds security bits).1
open _root_.P2M9e1cfc64 renaming h272 → _p2mH272
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h275 (security bits : ℕ) (output : Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(LocalPairProgram.activationApprox security bits : ℝ) * (primary security bits output.val : ℝ) -
      activation security * (primaryLaw security).weight output| ≤
      (1 / 2 + 64 * (Parameters.base security : ℝ) * Parameters.dimension security) * (1 / (2 : ℝ)^bits) := by
  have hp : |(primary security bits output.val : ℝ) - (primaryLaw security).weight output| ≤
      (64 * (Parameters.base security : ℝ) * Parameters.dimension security) * (1 / (2 : ℝ)^bits) := by
    simpa only [primaryLaw] using _p2mH392 security bits output hprecision hbudget
  have ha := _p2mH130 security bits
  have hpa : 0 ≤ (primary security bits output.val : ℝ) := (approximatePrimaryLaw security bits).nonneg output
  have hpa1 := (approximatePrimaryLaw security bits).atom_le_one output
  have har : |activation security| ≤ 1 := by
    rw [abs_of_pos (activation_pos security)]
    exact (activation_le_half security).trans (by norm_num)
  calc
    _ = |((LocalPairProgram.activationApprox security bits : ℝ) - activation security) *
          (primary security bits output.val : ℝ) + activation security *
          ((primary security bits output.val : ℝ) - (primaryLaw security).weight output)| := by congr 1; ring
    _ ≤ |(LocalPairProgram.activationApprox security bits : ℝ) - activation security| * (primary security bits output.val : ℝ) +
      |activation security| * |(primary security bits output.val : ℝ) - (primaryLaw security).weight output| := by
        simpa only [abs_mul, abs_of_nonneg hpa] using abs_add_le
          (((LocalPairProgram.activationApprox security bits : ℝ) - activation security) * (primary security bits output.val : ℝ))
          (activation security * ((primary security bits output.val : ℝ) - (primaryLaw security).weight output))
    _ ≤ ((1 / 2 : ℝ) * (1 / (2 : ℝ)^bits)) * 1 +
      1 * ((64 * (Parameters.base security : ℝ) * Parameters.dimension security) * (1 / (2 : ℝ)^bits)) :=
        add_le_add (mul_le_mul ha hpa1 hpa (by positivity)) (mul_le_mul har hp (abs_nonneg _) (by norm_num))
    _ = _ := by ring
open _root_.P2M9e1cfc64 renaming h275 → _p2mH275
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h268 (security : ℕ) (profile : Palette security → ℝ) (bound : ℝ) (hb : 0 ≤ bound)
    (hprofile : ∀ color, |profile color| ≤ bound) (output : Palette security) :
    |actual security profile output| ≤ RationalTensorInverseProgram.actualBound security * bound := by
  have hq := FirstResponse.modulus_pos security
  have hbase := FirstResponse.base_pos security
  have hden := _p2mH269 security output
  have hpos : 0 < activation security * (primaryLaw security).weight output :=
    mul_pos (activation_pos security) (primaryReference_positive security output)
  rw [_p2mH270, abs_div, abs_of_pos hpos]
  calc
    _ ≤ (RationalDensityInverseProgram.inverseBound security * bound) /
      (activation security * (primaryLaw security).weight output) :=
      div_le_div_of_nonneg_right
        (_p2mH177 security profile bound hb hprofile output) hpos.le
    _ ≤ (RationalDensityInverseProgram.inverseBound security * bound) /
      (1 / (8 * (Parameters.base security : ℝ) * Parameters.modulus security)) :=
      div_le_div_of_nonneg_left (by unfold RationalDensityInverseProgram.inverseBound; positivity) (by positivity) hden
    _ = _ := by unfold RationalTensorInverseProgram.actualBound; ring_nf; simp only [inv_inv]
open _root_.P2M9e1cfc64 renaming h268 → _p2mH268
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h271 (security : ℕ) (first second : Palette security → ℝ)
    (error : ℝ) (he : 0 ≤ error) (hdiff : ∀ color, |first color - second color| ≤ error) (output : Palette security) :
    |actual security first output - actual security second output| ≤ RationalTensorInverseProgram.actualBound security * error := by
  have h := _p2mH268 security (first - second) error he hdiff output
  simpa only [map_sub, Pi.sub_apply] using h
open _root_.P2M9e1cfc64 renaming h271 → _p2mH271
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h277 (security : ℕ) (profile : Palette security → ℝ) (word : Fin 1 → Palette security) :
    PrimaryTensorInverse.massLift security 1 (PrimaryMassFamilies.oneWordProfile profile) word =
      actual security profile (word 0) := by
  unfold PrimaryTensorInverse.massLift
  change PrimaryTensorInverse.densityInverse security
    (fun color => PrimaryTensorInverse.massDensity security 1 (PrimaryMassFamilies.oneWordProfile profile)
      (Fin.cons color Fin.elim0)) (word 0) =
    PrimaryTensorInverse.densityInverse security (RootTaggedLocal.profileDensity security profile) (word 0)
  apply congrArg (fun input : Palette security → ℝ => PrimaryTensorInverse.densityInverse security input (word 0))
  funext color
  simp only [PrimaryTensorInverse.massDensity, PrimaryTensorInverse.referenceWeight, PrimaryMassFamilies.oneWordProfile,
    Fin.prod_univ_one, Fin.cons_zero, RootTaggedLocal.profileDensity_apply]
open _root_.P2M9e1cfc64 renaming h277 → _p2mH277
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h276 (security : ℕ) : 0 ≤ errorConstant security := by
  unfold errorConstant RationalDensityInverseProgram.inverseBound RationalFirstResponseProgram.inverseErrorConstant
  positivity
open _root_.P2M9e1cfc64 renaming h276 → _p2mH276
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h273 (security bits : ℕ) (profile : ℕ → ℚ) (bound : ℝ) (hb : 0 ≤ bound)
    (hprofile : ∀ color : Palette security, |(profile color.val : ℝ)| ≤ bound)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(current security bits profile output.val : ℝ) - actual security (fun color => (profile color.val : ℝ)) output| ≤
      errorConstant security * bound * (1 / (2 : ℝ)^bits) := by
  let lower : ℝ := 1 / (32 * (Parameters.base security : ℝ) * Parameters.modulus security)
  have hb0 := FirstResponse.base_pos security
  have hq0 := FirstResponse.modulus_pos security
  have hi : 0 ≤ RationalFirstResponseProgram.inverseErrorConstant security := by
    unfold RationalFirstResponseProgram.inverseErrorConstant
    positivity
  have hprimary : lower ≤ activation security * (primaryLaw security).weight output := by
    apply le_trans _ (_p2mH269 security output)
    dsimp only [lower]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h := _p2mH179
    (RationalFirstResponseProgram.inverse security bits profile output.val : ℝ)
    ((FirstResponse.responseEquiv security).symm (fun color : Palette security => (profile color.val : ℝ)) output)
    ((LocalPairProgram.activationApprox security bits : ℝ) * (primary security bits output.val : ℝ))
    (activation security * (primaryLaw security).weight output) lower
    (RationalFirstResponseProgram.inverseErrorConstant security * bound * (1 / (2 : ℝ)^bits))
    ((1 / 2 + 64 * (Parameters.base security : ℝ) * Parameters.dimension security) * (1 / (2 : ℝ)^bits))
    (RationalDensityInverseProgram.inverseBound security * bound) (by dsimp only [lower]; positivity)
    (_p2mH272 security bits output hfirst) hprimary (by positivity) (by positivity)
    (by unfold RationalDensityInverseProgram.inverseBound; positivity)
    ((_p2mH224 security bits profile output bound hb hprofile hfirst).trans_eq (by ring))
    (_p2mH275 security bits output hprecision hbudget)
    (_p2mH177 security _ bound hb hprofile output)
  rw [current, Rat.cast_div, Rat.cast_mul, _p2mH270]
  apply h.trans_eq
  unfold errorConstant lower
  ring_nf
  simp only [inv_inv]
  ring
open _root_.P2M9e1cfc64 renaming h273 → _p2mH273
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h274 (security bits : ℕ) (computed : ℕ → ℚ) (profile : Palette security → ℝ)
    (bound profileError : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ profileError)
    (hcomputed : ∀ color : Palette security, |(computed color.val : ℝ)| ≤ bound)
    (hdiff : ∀ color : Palette security, |(computed color.val : ℝ) - profile color| ≤ profileError)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(current security bits computed output.val : ℝ) - actual security profile output| ≤
      errorConstant security * bound * (1 / (2 : ℝ)^bits) + RationalTensorInverseProgram.actualBound security * profileError := by
  exact (abs_sub_le _ (actual security (fun color => (computed color.val : ℝ)) output) _).trans
    (add_le_add (_p2mH273 security bits computed bound hb hcomputed hfirst hprecision hbudget output)
      (_p2mH271 security _ profile profileError he hdiff output))
open _root_.P2M9e1cfc64 renaming h274 → _p2mH274
end
open _root_.P2M9e1cfc64 renaming h268 → _p2mH268
open _root_.P2M9e1cfc64 renaming h269 → _p2mH269
open _root_.P2M9e1cfc64 renaming h270 → _p2mH270
open _root_.P2M9e1cfc64 renaming h271 → _p2mH271
open _root_.P2M9e1cfc64 renaming h272 → _p2mH272
open _root_.P2M9e1cfc64 renaming h273 → _p2mH273
open _root_.P2M9e1cfc64 renaming h274 → _p2mH274
open _root_.P2M9e1cfc64 renaming h275 → _p2mH275
open _root_.P2M9e1cfc64 renaming h276 → _p2mH276
open _root_.P2M9e1cfc64 renaming h277 → _p2mH277
end CurrentAFT.RationalMassLiftProgram
open _root_.P2M9e1cfc64 renaming h268 → _p2mH268
open _root_.P2M9e1cfc64 renaming h269 → _p2mH269
open _root_.P2M9e1cfc64 renaming h270 → _p2mH270
open _root_.P2M9e1cfc64 renaming h271 → _p2mH271
open _root_.P2M9e1cfc64 renaming h272 → _p2mH272
open _root_.P2M9e1cfc64 renaming h273 → _p2mH273
open _root_.P2M9e1cfc64 renaming h274 → _p2mH274
open _root_.P2M9e1cfc64 renaming h275 → _p2mH275
open _root_.P2M9e1cfc64 renaming h276 → _p2mH276
open _root_.P2M9e1cfc64 renaming h277 → _p2mH277
end
open _root_.P2M9e1cfc64 renaming h273 → _p2mH273
open _root_.P2M9e1cfc64 renaming h268 → _p2mH268
open _root_.P2M9e1cfc64 renaming h275 → _p2mH275
open _root_.P2M9e1cfc64 renaming h272 → _p2mH272
open _root_.P2M9e1cfc64 renaming h277 → _p2mH277
open _root_.P2M9e1cfc64 renaming h271 → _p2mH271
open _root_.P2M9e1cfc64 renaming h269 → _p2mH269
open _root_.P2M9e1cfc64 renaming h276 → _p2mH276
open _root_.P2M9e1cfc64 renaming h274 → _p2mH274
open _root_.P2M9e1cfc64 renaming h270 → _p2mH270
section
namespace CurrentAFT.RationalBackgroundProfiles
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary BackgroundCertificates BackgroundTranslations
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus Parameters.base Parameters.safeMargin
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h156 (security : ℕ) : margin security = Parameters.safeMargin security := by
  simp only [margin, Parameters.safeMargin, Parameters.sourceCutoff, Parameters.base]
open _root_.P2M9e1cfc64 renaming h156 → _p2mH156
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h157 (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    (shifted security shift output.val:ℝ) = (shiftedSafeLaw security shift).weight output := by
  unfold shifted
  rw [colors, PublicParameterProgram.modulus_value, _p2mH156]
  exact RationalProposalProgram.bodyKernel_cast security shift output
open _root_.P2M9e1cfc64 renaming h157 → _p2mH157
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h155 (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    inverseShift security shift output.val = ((shiftEquiv security shift).symm output).val := by
  rw [_p2mH145]
  have h := (RationalProposalProgram.shift_condition security (-shift) output (shiftEquiv security (-shift) output)).mp rfl
  have hh := congrArg Int.toNat h
  simpa only [inverseShift, colors, PublicParameterProgram.modulus_value, sub_eq_add_neg, Int.toNat_natCast] using hh
open _root_.P2M9e1cfc64 renaming h155 → _p2mH155
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h152 (security bits : ℕ) (profile : ℕ → ℚ) (output : FirstHistogram.Palette security) :
    (convolution security bits profile output.val:ℝ) =
      (RationalProposalProgram.approximateSeedLaw security bits).expectation (fun seed =>
        (profile ((shiftEquiv security (actualBlur security seed)).symm output).val:ℝ)) := by
  rw [convolution, RationalProposalProgram.seedEvaluate_cast]
  apply congrArg (FiniteDist.expectation (RationalProposalProgram.approximateSeedLaw security bits))
  funext seed
  rw [_p2mH155]
  rfl
open _root_.P2M9e1cfc64 renaming h152 → _p2mH152
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h153 (security bits : ℕ) (profile : ℕ → ℚ) (ideal : FirstHistogram.Palette security → ℝ)
    (hprofile : ∀ output, (profile output.val:ℝ) = ideal output) (bound : ℝ)
    (hbound : ∀ output, |ideal output| ≤ bound) (output : FirstHistogram.Palette security) :
    |(convolution security bits profile output.val:ℝ)-rootConvolutionProfile security ideal output| ≤
      bound*(3/(2:ℝ)^bits) := by
  rw [_p2mH152]
  simp_rw [hprofile]
  exact (_p2mH70 (RationalProposalProgram.approximateSeedLaw security bits)
    (actualSeedLaw security) (fun seed => ideal ((shiftEquiv security (actualBlur security seed)).symm output)) bound
    (fun seed => hbound _)).trans
    (mul_le_mul_of_nonneg_left (_p2mH393 security bits)
      ((abs_nonneg (ideal output)).trans (hbound output)))
open _root_.P2M9e1cfc64 renaming h153 → _p2mH153
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h154 (security bits : ℕ) (profile : ℕ → ℚ) (ideal : FirstHistogram.Palette security → ℝ)
    (bound profileError : ℝ) (hbound : ∀ output : FirstHistogram.Palette security, |(profile output.val:ℝ)| ≤ bound)
    (hdiff : ∀ output : FirstHistogram.Palette security, |(profile output.val:ℝ)-ideal output| ≤ profileError)
    (output : FirstHistogram.Palette security) :
    |(convolution security bits profile output.val:ℝ)-rootConvolutionProfile security ideal output| ≤
      bound*(3/(2:ℝ)^bits)+profileError := by
  have hfirst := _p2mH153 security bits profile (fun color => (profile color.val:ℝ))
    (fun _ => rfl) bound hbound output
  have hsecond := _p2mH48 (actualSeedLaw security)
    (fun seed => (profile ((shiftEquiv security (actualBlur security seed)).symm output).val:ℝ)-
      ideal ((shiftEquiv security (actualBlur security seed)).symm output)) profileError (fun seed => hdiff _)
  have hs : |rootConvolutionProfile security (fun color => (profile color.val:ℝ)) output-
      rootConvolutionProfile security ideal output| ≤ profileError := by
    simpa only [rootConvolutionProfile, FiniteDist.expectation, mul_sub, Finset.sum_sub_distrib] using hsecond
  exact (abs_sub_le _ (rootConvolutionProfile security (fun color => (profile color.val:ℝ)) output) _).trans
    (add_le_add hfirst hs)
open _root_.P2M9e1cfc64 renaming h154 → _p2mH154
end
open _root_.P2M9e1cfc64 renaming h152 → _p2mH152
open _root_.P2M9e1cfc64 renaming h153 → _p2mH153
open _root_.P2M9e1cfc64 renaming h154 → _p2mH154
open _root_.P2M9e1cfc64 renaming h155 → _p2mH155
open _root_.P2M9e1cfc64 renaming h156 → _p2mH156
open _root_.P2M9e1cfc64 renaming h157 → _p2mH157
end CurrentAFT.RationalBackgroundProfiles
open _root_.P2M9e1cfc64 renaming h152 → _p2mH152
open _root_.P2M9e1cfc64 renaming h153 → _p2mH153
open _root_.P2M9e1cfc64 renaming h154 → _p2mH154
open _root_.P2M9e1cfc64 renaming h155 → _p2mH155
open _root_.P2M9e1cfc64 renaming h156 → _p2mH156
open _root_.P2M9e1cfc64 renaming h157 → _p2mH157
end
open _root_.P2M9e1cfc64 renaming h153 → _p2mH153
open _root_.P2M9e1cfc64 renaming h152 → _p2mH152
open _root_.P2M9e1cfc64 renaming h156 → _p2mH156
open _root_.P2M9e1cfc64 renaming h157 → _p2mH157
open _root_.P2M9e1cfc64 renaming h155 → _p2mH155
open _root_.P2M9e1cfc64 renaming h154 → _p2mH154
section
namespace CurrentAFT.RationalRootProfileProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls
  RootTaggedLocal
open UniformBodyProfiles (BodyRole preRootLaw)
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base primaryLaw centerLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h421 (security bits output : ℕ) :
    attachment security bits output =
      ∑ scalar : Window ((security+2)^2-1),
        RationalProposalProgram.gaussianWeight security ((security+2)^2-1) bits scalar *
          RationalBackgroundProfiles.shifted security scalar.val output := by
  unfold attachment
  exact (FiniteConvolutionProgram.windowIndexEquiv ((security+2)^2-1)).sum_comp
    (fun scalar : Window ((security+2)^2-1) =>
      RationalProposalProgram.gaussianWeight security ((security+2)^2-1) bits scalar *
        RationalBackgroundProfiles.shifted security scalar.val output)
open _root_.P2M9e1cfc64 renaming h421 → _p2mH421
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h434 (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : Palette security) :
    (preRoot security bits role queue output.val : ℝ) = (approximatePreRoot security bits role queue).weight output := by
  cases role with
  | free => rfl
  | queue => exact _p2mH157 security queue output
  | attachment =>
    have hcutoff : (security + 2)^2 - 1 = Parameters.sourceCutoff security - 1 := by
      simp only [Parameters.sourceCutoff, Parameters.base]
    unfold preRoot
    rw [_p2mH421, hcutoff]
    simp only [Rat.cast_sum, Rat.cast_mul, RationalProposalProgram.gaussianWeight_eq,
      _p2mH157, approximatePreRoot, FiniteDist.mix_weight, windowApproxLaw]
    rfl
open _root_.P2M9e1cfc64 renaming h434 → _p2mH434
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h433 (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : Palette security) :
    |(preRoot security bits role queue output.val : ℝ)| ≤ 1 := by
  rw [_p2mH434, abs_of_nonneg ((approximatePreRoot security bits role queue).nonneg output)]
  exact (approximatePreRoot security bits role queue).atom_le_one output
open _root_.P2M9e1cfc64 renaming h433 → _p2mH433
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h432 (security : ℕ) : 1 ≤ preRootError security := by
  have h : 0 ≤ RationalRootMassProgram.primaryErrorConstant security * (Parameters.modulus security : ℝ) := by
    unfold RationalRootMassProgram.primaryErrorConstant
    positivity
  unfold preRootError
  linarith
open _root_.P2M9e1cfc64 renaming h432 → _p2mH432
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h435 (security bits : ℕ) (role : BodyRole) (queue : ℤ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(preRoot security bits role queue output.val : ℝ) - (preRootLaw security role queue).weight output| ≤
      preRootError security * (1 / (2 : ℝ)^bits) := by
  have he : 0 ≤ 1 / (2 : ℝ)^bits := by positivity
  cases role with
  | free =>
    have h := _p2mH384 security bits output hprecision hbudget
    have hsame : |(preRoot security bits .free queue output.val : ℝ) - (preRootLaw security .free queue).weight output| ≤
        (RationalRootMassProgram.primaryErrorConstant security * Parameters.modulus security + 2) * (1 / (2 : ℝ)^bits) := by
      simpa only [preRoot, preRootLaw, centerLaw, RationalRootMassProgram.primaryErrorConstant] using h
    exact hsame.trans (mul_le_mul_of_nonneg_right (by unfold preRootError; linarith) he)
  | queue =>
    rw [_p2mH434]
    change |(preRootLaw security .queue queue).weight output - (preRootLaw security .queue queue).weight output| ≤ _
    rw [sub_self, abs_zero]
    exact mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (_p2mH432 security)) he
  | attachment =>
    rw [_p2mH434]
    let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits
    let test := fun scalar : LocalReferenceEnergy.Scalar security => ((safeLaw security).map (shiftEquiv security scalar.val)).weight output
    change |approximate.expectation test - (scalarLaw security).expectation test| ≤ _
    have htest (scalar : LocalReferenceEnergy.Scalar security) : |test scalar| ≤ 1 := by
      rw [abs_of_nonneg (((safeLaw security).map (shiftEquiv security scalar.val)).nonneg output)]
      exact ((safeLaw security).map (shiftEquiv security scalar.val)).atom_le_one output
    have hdiff := _p2mH70 approximate (scalarLaw security) test 1 htest
    have hl1 : (∑ scalar, |approximate.weight scalar - (scalarLaw security).weight scalar|) ≤ 1 / (2 : ℝ)^bits :=
      _p2mH14 _ _ _ _ (_p2mH549 security)
        (_p2mH550 security).symm
    apply hdiff.trans
    rw [one_mul]
    exact hl1.trans ((by simpa only [one_mul] using mul_le_mul_of_nonneg_right (_p2mH432 security) he))
open _root_.P2M9e1cfc64 renaming h435 → _p2mH435
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h436 (security bits : ℕ) (role : BodyRole) (queue root : ℤ) (output : Palette security) :
    |(shifted security bits role queue root output.val : ℝ)| ≤ 1 := by
  rw [shifted, _p2mH155]
  exact _p2mH433 security bits role queue _
open _root_.P2M9e1cfc64 renaming h436 → _p2mH436
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h437 (security bits : ℕ) (role : BodyRole) (queue : ℤ) (root : CycleRootExpansion.Root security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(shifted security bits role queue root.val output.val : ℝ) - (shiftedLaw security role queue root).weight output| ≤
      preRootError security * (1 / (2 : ℝ)^bits) := by
  rw [shifted, _p2mH155, shiftedLaw, FiniteDist.map_equiv_weight]
  exact _p2mH435 security bits role queue hprecision hbudget _
open _root_.P2M9e1cfc64 renaming h437 → _p2mH437
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h429 (security : ℕ) (role : BodyRole) (queue : ℤ) (output : Palette security) :
    (meanLaw security role queue).weight output =
      BackgroundCertificates.rootConvolutionProfile security (preRootLaw security role queue).weight output := by
  unfold meanLaw shiftedLaw
  rw [_p2mH484, _p2mH47]
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  rfl
open _root_.P2M9e1cfc64 renaming h429 → _p2mH429
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h430 (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : Palette security) :
    |(mean security bits role queue output.val : ℝ)| ≤ 1 := by
  rw [mean, _p2mH152]
  exact _p2mH48 (RationalProposalProgram.approximateSeedLaw security bits) _ 1
    (fun seed => _p2mH433 security bits role queue _)
open _root_.P2M9e1cfc64 renaming h430 → _p2mH430
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h431 (security bits : ℕ) (role : BodyRole) (queue : ℤ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(mean security bits role queue output.val : ℝ) - (meanLaw security role queue).weight output| ≤
      (3 + preRootError security) * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH429]
  exact (_p2mH154 security bits (preRoot security bits role queue)
    (preRootLaw security role queue).weight 1 (preRootError security * (1 / (2 : ℝ)^bits))
    (_p2mH433 security bits role queue)
    (_p2mH435 security bits role queue hprecision hbudget) output).trans_eq (by ring)
open _root_.P2M9e1cfc64 renaming h431 → _p2mH431
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h423 (security bits : ℕ) (role : BodyRole) (queue root : ℤ) (output : Palette security) :
    |(deviation security bits role queue root output.val : ℝ)| ≤ 2 := by
  rw [deviation, Rat.cast_sub]
  exact (abs_sub _ _).trans ((add_le_add (_p2mH436 security bits role queue root output)
    (_p2mH430 security bits role queue output)).trans_eq (by norm_num))
open _root_.P2M9e1cfc64 renaming h423 → _p2mH423
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h424 (security bits : ℕ) (role : BodyRole) (queue : ℤ) (root : CycleRootExpansion.Root security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(deviation security bits role queue root.val output.val : ℝ) - deviationProfile security role queue root output| ≤
      (2 * preRootError security + 3) * (1 / (2 : ℝ)^bits) := by
  rw [deviation, Rat.cast_sub, deviationProfile, Pi.sub_apply]
  have htriangle :
      |(shifted security bits role queue root.val output.val : ℝ) - (mean security bits role queue output.val : ℝ) -
          ((shiftedLaw security role queue root).weight output - (meanLaw security role queue).weight output)| ≤
        |(shifted security bits role queue root.val output.val : ℝ) - (shiftedLaw security role queue root).weight output| +
          |(mean security bits role queue output.val : ℝ) - (meanLaw security role queue).weight output| := by
    calc
      _ = |((shifted security bits role queue root.val output.val : ℝ) - (shiftedLaw security role queue root).weight output) -
          ((mean security bits role queue output.val : ℝ) - (meanLaw security role queue).weight output)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  exact htriangle.trans ((add_le_add (_p2mH437 security bits role queue root hprecision hbudget output)
    (_p2mH431 security bits role queue hprecision hbudget output)).trans_eq (by ring))
open _root_.P2M9e1cfc64 renaming h424 → _p2mH424
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h427 (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : Palette security) :
    |(meanDeviation security bits role queue output.val : ℝ)| ≤ 2 := by
  rw [meanDeviation, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    PublicParameterProgram.modulus_value]
  have hq : (1 : ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt (show 0 < Parameters.modulus security from by
      exact_mod_cast FirstResponse.modulus_pos security)))
  have hu : |(1 : ℝ) / Parameters.modulus security| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hq
  exact (abs_sub _ _).trans ((add_le_add (_p2mH430 security bits role queue output)
    hu).trans_eq (by norm_num))
open _root_.P2M9e1cfc64 renaming h427 → _p2mH427
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h428 (security bits : ℕ) (role : BodyRole) (queue : ℤ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(meanDeviation security bits role queue output.val : ℝ) - RootMeanPrimary.meanProfile security role queue output| ≤
      (3 + preRootError security) * (1 / (2 : ℝ)^bits) := by
  rw [meanDeviation, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    PublicParameterProgram.modulus_value]
  simpa only [RootMeanPrimary.meanProfile, Pi.sub_apply, LocalReferenceEnergy.uniformReference_weight,
    sub_sub_sub_cancel_right] using
      _p2mH431 security bits role queue hprecision hbudget output
open _root_.P2M9e1cfc64 renaming h428 → _p2mH428
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h422 (security : ℕ) :
    0 ≤ firstErrorConstant security ∧ 0 ≤ meanErrorConstant security := by
  have hp := _p2mH432 security
  have hm := _p2mH276 security
  have ha := _p2mH455 security
  constructor
  · unfold firstErrorConstant; positivity
  · unfold meanErrorConstant; positivity
open _root_.P2M9e1cfc64 renaming h422 → _p2mH422
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h425 (security bits : ℕ) (role : BodyRole) (queue : ℤ) (root : CycleRootExpansion.Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(firstDensity security bits role queue root.val output.val : ℝ) -
      RootReferenceColumns.singletonDensityAt security role queue root output| ≤
      firstErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have hp := _p2mH432 security
  have h := _p2mH274 security bits
    (deviation security bits role queue root.val) (deviationProfile security role queue root) 2
    ((2 * preRootError security + 3) * (1 / (2 : ℝ)^bits)) (by norm_num) (by positivity)
    (_p2mH423 security bits role queue root.val)
    (_p2mH424 security bits role queue root hprecision hbudget) hfirst hprecision hbudget output
  change |(firstDensity security bits role queue root.val output.val : ℝ) -
    RootReferenceColumns.singletonDensityAt security role queue root output| ≤ _ at h
  exact h.trans_eq (by unfold firstErrorConstant; ring)
open _root_.P2M9e1cfc64 renaming h425 → _p2mH425
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h426 (security bits : ℕ) (role : BodyRole) (queue : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(meanDensity security bits role queue output.val : ℝ) -
      RationalMassLiftProgram.actual security (RootMeanPrimary.meanProfile security role queue) output| ≤
      meanErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have hp := _p2mH432 security
  exact (_p2mH274 security bits
    (meanDeviation security bits role queue) (RootMeanPrimary.meanProfile security role queue) 2
    ((3 + preRootError security) * (1 / (2 : ℝ)^bits)) (by norm_num) (by positivity)
    (_p2mH427 security bits role queue)
    (_p2mH428 security bits role queue hprecision hbudget) hfirst hprecision hbudget output).trans_eq
      (by unfold meanErrorConstant; ring)
open _root_.P2M9e1cfc64 renaming h426 → _p2mH426
end
open _root_.P2M9e1cfc64 renaming h421 → _p2mH421
open _root_.P2M9e1cfc64 renaming h422 → _p2mH422
open _root_.P2M9e1cfc64 renaming h423 → _p2mH423
open _root_.P2M9e1cfc64 renaming h424 → _p2mH424
open _root_.P2M9e1cfc64 renaming h425 → _p2mH425
open _root_.P2M9e1cfc64 renaming h426 → _p2mH426
open _root_.P2M9e1cfc64 renaming h427 → _p2mH427
open _root_.P2M9e1cfc64 renaming h428 → _p2mH428
open _root_.P2M9e1cfc64 renaming h429 → _p2mH429
open _root_.P2M9e1cfc64 renaming h430 → _p2mH430
open _root_.P2M9e1cfc64 renaming h431 → _p2mH431
open _root_.P2M9e1cfc64 renaming h432 → _p2mH432
open _root_.P2M9e1cfc64 renaming h433 → _p2mH433
open _root_.P2M9e1cfc64 renaming h434 → _p2mH434
open _root_.P2M9e1cfc64 renaming h435 → _p2mH435
open _root_.P2M9e1cfc64 renaming h436 → _p2mH436
open _root_.P2M9e1cfc64 renaming h437 → _p2mH437
end CurrentAFT.RationalRootProfileProgram
open _root_.P2M9e1cfc64 renaming h421 → _p2mH421
open _root_.P2M9e1cfc64 renaming h422 → _p2mH422
open _root_.P2M9e1cfc64 renaming h423 → _p2mH423
open _root_.P2M9e1cfc64 renaming h424 → _p2mH424
open _root_.P2M9e1cfc64 renaming h425 → _p2mH425
open _root_.P2M9e1cfc64 renaming h426 → _p2mH426
open _root_.P2M9e1cfc64 renaming h427 → _p2mH427
open _root_.P2M9e1cfc64 renaming h428 → _p2mH428
open _root_.P2M9e1cfc64 renaming h429 → _p2mH429
open _root_.P2M9e1cfc64 renaming h430 → _p2mH430
open _root_.P2M9e1cfc64 renaming h431 → _p2mH431
open _root_.P2M9e1cfc64 renaming h432 → _p2mH432
open _root_.P2M9e1cfc64 renaming h433 → _p2mH433
open _root_.P2M9e1cfc64 renaming h434 → _p2mH434
open _root_.P2M9e1cfc64 renaming h435 → _p2mH435
open _root_.P2M9e1cfc64 renaming h436 → _p2mH436
open _root_.P2M9e1cfc64 renaming h437 → _p2mH437
end
open _root_.P2M9e1cfc64 renaming h421 → _p2mH421
open _root_.P2M9e1cfc64 renaming h423 → _p2mH423
open _root_.P2M9e1cfc64 renaming h422 → _p2mH422
open _root_.P2M9e1cfc64 renaming h437 → _p2mH437
open _root_.P2M9e1cfc64 renaming h429 → _p2mH429
open _root_.P2M9e1cfc64 renaming h424 → _p2mH424
open _root_.P2M9e1cfc64 renaming h428 → _p2mH428
open _root_.P2M9e1cfc64 renaming h431 → _p2mH431
open _root_.P2M9e1cfc64 renaming h433 → _p2mH433
open _root_.P2M9e1cfc64 renaming h425 → _p2mH425
open _root_.P2M9e1cfc64 renaming h436 → _p2mH436
open _root_.P2M9e1cfc64 renaming h430 → _p2mH430
open _root_.P2M9e1cfc64 renaming h435 → _p2mH435
open _root_.P2M9e1cfc64 renaming h427 → _p2mH427
open _root_.P2M9e1cfc64 renaming h434 → _p2mH434
open _root_.P2M9e1cfc64 renaming h426 → _p2mH426
open _root_.P2M9e1cfc64 renaming h432 → _p2mH432
section
namespace CurrentAFT.RationalBackgroundTable
open AFT ControlCoordinates ControlProduct GradedControlAlgebra BackgroundFamilies
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalBackgroundTable.tableFinDecidableEq
set_option maxRecDepth 8192
private theorem _root_.P2M9e1cfc64.h557 (order : ℕ) (horder : 1 ≤ order) (arity : TruncatedArity order) :
    arity = primaryArity order horder ↔ arity.val.1.val = 1 ∧ arity.val.2.val = 0 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · intro h
    apply Subtype.ext
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
open _root_.P2M9e1cfc64 renaming h557 → _p2mH557
set_option maxRecDepth 8192
private theorem _root_.P2M9e1cfc64.h556 (order : ℕ) (horder : 1 ≤ order) (arity : TruncatedArity order) :
    arity = bodyArity order horder ↔ arity.val.1.val = 0 ∧ arity.val.2.val = 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · intro h
    apply Subtype.ext
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
open _root_.P2M9e1cfc64 renaming h556 → _p2mH556
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h158 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order)
    (first : Primary → ℝ) (second : Body → ℝ)
    (hf : ∑ color, primary.weight color*first color = 0) (hs : ∑ color, body.weight color*second color = 0) :
    firstTable order first second = fun arity =>
      ((primaryFamily primary body order horder first hf+bodyFamily primary body order horder second hs) arity).val := by
  funext arity colors centers
  by_cases hp : arity = primaryArity order horder
  · subst arity
    simp [firstTable, primaryFamily, bodyFamily, primaryArity, bodyArity, primaryKernel, bodyKernel]
  · by_cases hb : arity = bodyArity order horder
    · subst arity
      simp [firstTable, primaryFamily, bodyFamily, primaryArity, bodyArity, primaryKernel, bodyKernel]
    · have hfirst := mt (_p2mH557 order horder arity).mpr hp
      have hsecond := mt (_p2mH556 order horder arity).mpr hb
      simp only [firstTable, dif_neg hfirst, dif_neg hsecond, Pi.add_apply, primaryFamily, bodyFamily,
        Pi.single_eq_of_ne hp, Pi.single_eq_of_ne hb, Submodule.coe_zero, Pi.zero_apply, add_zero]
open _root_.P2M9e1cfc64 renaming h158 → _p2mH158
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h159 {Primary Body : Type*} (order : ℕ) (firstQ secondQ : ℕ → ℚ)
    (first : Primary → ℝ) (second : Body → ℝ) (primaryCode : Primary → ℕ) (bodyCode : Body → ℕ)
    (firstError secondError : ℝ) (hf : 0 ≤ firstError) (hs : 0 ≤ secondError)
    (hfirst : ∀ color, |(firstQ (primaryCode color):ℝ)-first color| ≤ firstError)
    (hsecond : ∀ color, |(secondQ (bodyCode color):ℝ)-second color| ≤ secondError)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary) (centers : Fin arity.val.2.val → Body) :
    |(firstTable order firstQ secondQ arity (fun index => primaryCode (colors index)) (fun index => bodyCode (centers index)):ℝ)-
      firstTable order first second arity colors centers| ≤ firstError+secondError := by
  unfold firstTable
  split_ifs
  · exact (hfirst _).trans (le_add_of_nonneg_right hs)
  · exact (hsecond _).trans (le_add_of_nonneg_left hf)
  · simpa only [Rat.cast_zero, sub_self, abs_zero] using add_nonneg hf hs
open _root_.P2M9e1cfc64 renaming h159 → _p2mH159
end
open _root_.P2M9e1cfc64 renaming h158 → _p2mH158
open _root_.P2M9e1cfc64 renaming h159 → _p2mH159
open _root_.P2M9e1cfc64 renaming h556 → _p2mH556
open _root_.P2M9e1cfc64 renaming h557 → _p2mH557
end CurrentAFT.RationalBackgroundTable
open _root_.P2M9e1cfc64 renaming h158 → _p2mH158
open _root_.P2M9e1cfc64 renaming h159 → _p2mH159
open _root_.P2M9e1cfc64 renaming h556 → _p2mH556
open _root_.P2M9e1cfc64 renaming h557 → _p2mH557
end
open _root_.P2M9e1cfc64 renaming h158 → _p2mH158
open _root_.P2M9e1cfc64 renaming h159 → _p2mH159
section
namespace CurrentAFT.RationalCoefficientExtraction
open AFT DiffuseProfiles ProposalPrimary ActualControls
  ControlCoordinates ControlProduct
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalCoefficientExtraction.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalCoefficientExtraction.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h175 (security degree : ℕ)
    (kernel : (Fin degree → Palette security) → ℝ) (permutation : Equiv.Perm (Fin degree))
    (output : Fin degree → Palette security) :
    PrimaryTensorInverse.tensorInverse security degree kernel (output ∘ permutation) =
      PrimaryTensorInverse.tensorInverse security degree (fun word => kernel (word ∘ permutation)) output := by
  change TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security) kernel (output ∘ permutation) =
    TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security) (fun word => kernel (word ∘ permutation)) output
  rw [TensorChannel.apply_formula_instance, TensorChannel.apply_formula_instance]
  rw [← (PrimaryTensorInverse.wordPermutation (Input := Palette security) degree permutation).sum_comp]
  apply Finset.sum_congr rfl
  intro source _
  congr 1
  exact Equiv.prod_comp permutation (fun index =>
    PrimaryTensorInverse.densityInverse security (Pi.single (source index) 1) (output index))
open _root_.P2M9e1cfc64 renaming h175 → _p2mH175
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h171 (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) :
    orderedDensity security mass selected = fun output =>
      LocalCoefficientFamily.selectedDensity security selected.card mass selected (by simp)
        (output ∘ orderPermutation selected) := by
  funext output
  unfold orderedDensity LocalCoefficientFamily.selectedDensity
  congr 1
  funext slot
  simp only [Function.comp_apply, orderPermutation, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl
open _root_.P2M9e1cfc64 renaming h171 → _p2mH171
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h174 (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) :
    (LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val =
      symmetrize (fun (colors : Fin selected.card → Palette security) (_ : Fin 0 → SafePalette security) =>
        PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security mass selected) colors) := by
  let raw : DensityKernel (Primary := Palette security) (Body := SafePalette security) selected.card 0 :=
    fun colors _ => LocalCoefficientFamily.normalizedSelectedDensity security selected.card mass selected (by simp) colors
  have hraw : (fun (colors : Fin selected.card → Palette security) (_ : Fin 0 → SafePalette security) =>
      PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security mass selected) colors) =
      reindexKernel (orderPermutation selected) (Equiv.refl (Fin 0)) raw := by
    funext colors centers
    rw [_p2mH171, ← _p2mH175]
    rfl
  rw [hraw, symmetrize_reindex_permutations]
  rfl
open _root_.P2M9e1cfc64 renaming h174 → _p2mH174
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h170 (security : ℕ) (source output : Palette security) :
    |(if source = output then (1 : ℝ) else 0) - 1 / (Parameters.modulus security : ℝ)| ≤ 1 := by
  have hq : (1 : ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_spec security).2.two_le.trans' (by omega)
  have hl : 0 ≤ 1 / (Parameters.modulus security : ℝ) := by positivity
  have hu : 1 / (Parameters.modulus security : ℝ) ≤ 1 :=
    (div_le_iff₀ (FirstResponse.modulus_pos security)).mpr (by simpa using hq)
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2M9e1cfc64 renaming h170 → _p2mH170
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h163 (security bits : ℕ) (source output : Palette security) :
    (atom security bits source.val output.val : ℝ) =
      ((if source = output then (1 : ℝ) else 0) - 1 / (Parameters.modulus security : ℝ)) /
        (RationalProposalProgram.approximatePrimaryLaw security bits).weight output := by
  unfold atom
  rw [PublicParameterProgram.modulus_value]
  by_cases hequal : source = output
  · subst output
    simp only [if_true, Rat.cast_div, Rat.cast_sub, Rat.cast_one, Rat.cast_natCast]
    rfl
  · have hne : source.val ≠ output.val := fun h => hequal (Fin.ext h)
    simp only [if_neg hne, if_neg hequal, Rat.cast_div, Rat.cast_sub, Rat.cast_zero, Rat.cast_one, Rat.cast_natCast]
    rfl
open _root_.P2M9e1cfc64 renaming h163 → _p2mH163
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h162 (security bits : ℕ) (source output : Palette security) :
    |(atom security bits source.val output.val : ℝ)| ≤ 4 * (Parameters.modulus security : ℝ) := by
  have hq0 := FirstResponse.modulus_pos security
  have hp := RationalProposalProgram.primary_lower security bits output
  have hpos : 0 < (RationalProposalProgram.approximatePrimaryLaw security bits).weight output :=
    (by positivity : (0 : ℝ) < 1 / (4 * (Parameters.modulus security : ℝ))).trans_le hp
  rw [_p2mH163, abs_div, abs_of_pos hpos]
  calc
    _ ≤ 1 / (RationalProposalProgram.approximatePrimaryLaw security bits).weight output :=
      div_le_div_of_nonneg_right (_p2mH170 security source output) hpos.le
    _ ≤ 1 / (1 / (4 * (Parameters.modulus security : ℝ))) :=
      one_div_le_one_div_of_le (by positivity) hp
    _ = _ := by simp only [one_div, inv_inv]
open _root_.P2M9e1cfc64 renaming h162 → _p2mH162
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h164 (security bits : ℕ) (source output : Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(atom security bits source.val output.val : ℝ) -
      MixedKernel.referenceAtom (primaryLaw security) (LocalReferenceEnergy.uniformReference security) source output| ≤
        atomErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have hq0 := FirstResponse.modulus_pos security
  have hlo : 1 / (4 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
    have h : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
      simpa only [primaryLaw] using primaryProfile_atom_lower security output
    have hscale : 1 / (4 * (Parameters.modulus security : ℝ)) ≤ 1 / (2 * (Parameters.modulus security : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    exact hscale.trans h
  have hp : |(RationalProposalProgram.approximatePrimaryLaw security bits).weight output - (primaryLaw security).weight output| ≤
      RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits) := by
    simpa only [RationalProposalProgram.approximatePrimaryLaw, primaryLaw, RationalRootMassProgram.primaryErrorConstant] using
      _p2mH392 security bits output hprecision hbudget
  rw [_p2mH163, MixedKernel.referenceAtom_eq, LocalReferenceEnergy.uniformReference_weight]
  have h := _p2mH179
    ((if source = output then (1 : ℝ) else 0) - 1 / (Parameters.modulus security : ℝ))
    ((if source = output then (1 : ℝ) else 0) - 1 / (Parameters.modulus security : ℝ))
    ((RationalProposalProgram.approximatePrimaryLaw security bits).weight output)
    ((primaryLaw security).weight output)
    (1 / (4 * (Parameters.modulus security : ℝ))) 0
    (RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits)) 1
    (by positivity) (RationalProposalProgram.primary_lower security bits output) hlo (by norm_num)
    (by unfold RationalRootMassProgram.primaryErrorConstant; positivity) (by norm_num)
    (by simp) hp (_p2mH170 security source output)
  apply h.trans_eq
  unfold atomErrorConstant
  ring_nf
  simp only [inv_inv]
open _root_.P2M9e1cfc64 renaming h164 → _p2mH164
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h160 (security : ℕ) (source output : Palette security) :
    |MixedKernel.referenceAtom (primaryLaw security) (LocalReferenceEnergy.uniformReference security) source output| ≤
      4 * (Parameters.modulus security : ℝ) := by
  have hq0 := FirstResponse.modulus_pos security
  have hp : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
    simpa only [primaryLaw] using primaryProfile_atom_lower security output
  rw [MixedKernel.referenceAtom_eq, LocalReferenceEnergy.uniformReference_weight, abs_div,
    abs_of_pos (primaryReference_positive security output)]
  calc
    _ ≤ 1 / (primaryLaw security).weight output :=
      div_le_div_of_nonneg_right (_p2mH170 security source output) (primaryReference_positive security output).le
    _ ≤ 1 / (1 / (2 * (Parameters.modulus security : ℝ))) :=
      one_div_le_one_div_of_le (by positivity) hp
    _ ≤ _ := by simp only [one_div, inv_inv]; linarith
open _root_.P2M9e1cfc64 renaming h160 → _p2mH160
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h166 (security bits : ℕ) (mass : (Fin 4 → ℕ) → ℚ) (selected : Finset (Fin 4))
    (output : Fin selected.card → Palette security) :
    (density security bits mass selected (fun index => (output index).val) : ℝ) =
      ∑ source : Fin 4 → Palette security, (mass (fun index => (source index).val) : ℝ) *
        ∏ slot : selected, (atom security bits (source slot.val).val (output (slotNumber selected slot)).val : ℝ) := by
  unfold density
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_prod]
  apply Finset.sum_congr (by ext; simp)
  intro source _
  congr 1
open _root_.P2M9e1cfc64 renaming h166 → _p2mH166
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h168 (bits : ℕ) : 1 / (2 : ℝ)^bits ≤ 1 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^bits)).mpr
  simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2^bits)
open _root_.P2M9e1cfc64 renaming h168 → _p2mH168
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h165 (security bits : ℕ) (mass : (Fin 4 → ℕ) → ℚ)
    (actualMass : (Fin 4 → Palette security) → ℝ) (selected : Finset (Fin 4))
    (massBound massError : ℝ) (hM : 0 ≤ massBound) (hE : 0 ≤ massError)
    (hmass : ∀ source, |actualMass source| ≤ massBound)
    (hdiff : ∀ source, |(mass (fun index => (source index).val) : ℝ) - actualMass source| ≤
      massError * (1 / (2 : ℝ)^bits)) (output : Fin selected.card → Palette security) :
    |(density security bits mass selected (fun index => (output index).val) : ℝ)| ≤
      extractionBound security selected.card massBound massError := by
  rw [_p2mH166]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _source : Fin 4 → Palette security,
        (massBound + massError) * (4 * (Parameters.modulus security : ℝ))^selected.card := by
      apply Finset.sum_le_sum
      intro source _
      have happrox : |(mass (fun index => (source index).val) : ℝ)| ≤ massBound + massError := by
        have h := abs_add_le ((mass (fun index => (source index).val) : ℝ) - actualMass source) (actualMass source)
        rw [sub_add_cancel] at h
        have hs := mul_le_mul_of_nonneg_left (_p2mH168 bits) hE
        linarith [hdiff source, hmass source]
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul happrox _ (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
      calc
        _ ≤ ∏ _slot : selected, 4 * (Parameters.modulus security : ℝ) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun slot _ => _p2mH162 security bits _ _)
        _ = _ := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      unfold extractionBound
      push_cast
      ring
open _root_.P2M9e1cfc64 renaming h165 → _p2mH165
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h167 (security bits : ℕ) (mass : (Fin 4 → ℕ) → ℚ)
    (actualMass : (Fin 4 → Palette security) → ℝ) (selected : Finset (Fin 4))
    (massBound massError : ℝ) (hM : 0 ≤ massBound) (hE : 0 ≤ massError)
    (hmass : ∀ source, |actualMass source| ≤ massBound)
    (hdiff : ∀ source, |(mass (fun index => (source index).val) : ℝ) - actualMass source| ≤
      massError * (1 / (2 : ℝ)^bits))
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) :
    |(density security bits mass selected (fun index => (output index).val) : ℝ) -
      orderedDensity security actualMass selected output| ≤
        extractionError security selected.card massBound massError * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let K : ℝ := 4 * Parameters.modulus security
  have hK : 1 ≤ K := by
    have hq : (2 : ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.two_le
    dsimp only [K]
    linarith
  have hA : 0 ≤ atomErrorConstant security := by
    unfold atomErrorConstant RationalRootMassProgram.primaryErrorConstant
    positivity
  rw [_p2mH166]
  unfold orderedDensity LocalTensors.referenceRestrictedComponent
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _source : Fin 4 → Palette security,
        (massError + massBound * selected.card * atomErrorConstant security) * K^selected.card * epsilon := by
      apply Finset.sum_le_sum
      intro source _
      let approxAtom := fun slot : selected =>
        (atom security bits (source slot.val).val (output (slotNumber selected slot)).val : ℝ)
      let trueAtom := fun slot : selected => MixedKernel.referenceAtom (primaryLaw security)
        (LocalReferenceEnergy.uniformReference security) (source slot.val) (output (slotNumber selected slot))
      have haprod : |∏ slot : selected, approxAtom slot| ≤ K^selected.card := by
        rw [Finset.abs_prod]
        calc
          _ ≤ ∏ _slot : selected, K := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
            (fun slot _ => _p2mH162 security bits _ _)
          _ = _ := by simp
      have hprod := _p2mH464 Finset.univ approxAtom trueAtom K
        (atomErrorConstant security * epsilon) hK (by positivity)
        (fun slot _ => _p2mH162 security bits _ _)
        (fun slot _ => _p2mH160 security _ _)
        (fun slot _ => _p2mH164 security bits _ _ hprecision hbudget)
      simp only [Finset.card_univ, Fintype.card_coe] at hprod
      change |(mass (fun index => (source index).val) : ℝ) * (∏ slot, approxAtom slot) -
        actualMass source * (∏ slot, trueAtom slot)| ≤ _
      calc
        _ = |((mass (fun index => (source index).val) : ℝ) - actualMass source) * (∏ slot, approxAtom slot) +
          actualMass source * ((∏ slot, approxAtom slot) - ∏ slot, trueAtom slot)| := by congr 1; ring
        _ ≤ |(mass (fun index => (source index).val) : ℝ) - actualMass source| * |∏ slot, approxAtom slot| +
          |actualMass source| * |(∏ slot, approxAtom slot) - ∏ slot, trueAtom slot| := by
            simpa only [abs_mul] using abs_add_le
              (((mass (fun index => (source index).val) : ℝ) - actualMass source) * (∏ slot, approxAtom slot))
              (actualMass source * ((∏ slot, approxAtom slot) - ∏ slot, trueAtom slot))
        _ ≤ (massError * epsilon) * K^selected.card +
          massBound * ((selected.card : ℝ) * (atomErrorConstant security * epsilon) * K^selected.card) :=
            add_le_add (mul_le_mul (hdiff source) haprod (abs_nonneg _) (by positivity))
              (mul_le_mul (hmass source) hprod (abs_nonneg _) hM)
        _ = _ := by ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      unfold extractionError
      dsimp only [K, epsilon]
      push_cast
      ring
open _root_.P2M9e1cfc64 renaming h167 → _p2mH167
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h169 (security bits : ℕ) (mass : (Fin 4 → ℕ) → ℚ)
    (actualMass : (Fin 4 → Palette security) → ℝ) (selected : Finset (Fin 4))
    (massBound massError : ℝ) (hM : 0 ≤ massBound) (hE : 0 ≤ massError)
    (hmass : ∀ source, |actualMass source| ≤ massBound)
    (hdiff : ∀ source, |(mass (fun index => (source index).val) : ℝ) - actualMass source| ≤
      massError * (1 / (2 : ℝ)^bits))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) :
    |(normalized security bits mass selected (fun index => (output index).val) : ℝ) -
      PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security actualMass selected) output| ≤
        normalizedError security selected.card massBound massError * (1 / (2 : ℝ)^bits) := by
  let approximate := fun source : Fin selected.card → Palette security =>
    (density security bits mass selected (fun index => (source index).val) : ℝ)
  have hbound : 0 ≤ extractionBound security selected.card massBound massError := by
    unfold extractionBound
    positivity
  have he : 0 ≤ extractionError security selected.card massBound massError := by
    unfold extractionError atomErrorConstant RationalRootMassProgram.primaryErrorConstant
    positivity
  have hprogram := _p2mH459 security bits selected.card
    (density security bits mass selected) (extractionBound security selected.card massBound massError) hbound
    (fun source => _p2mH165 security bits mass actualMass selected massBound massError hM hE hmass hdiff source)
    hfirst hprecision hbudget output
  have hreal := _p2mH457 security selected.card
    approximate (orderedDensity security actualMass selected)
    (extractionError security selected.card massBound massError * (1 / (2 : ℝ)^bits)) (by positivity)
    (fun source => _p2mH167 security bits mass actualMass selected massBound massError hM hE hmass hdiff
      hprecision hbudget source) output
  unfold normalized
  calc
    _ ≤ |(RationalTensorInverseProgram.current security bits selected.card (density security bits mass selected)
          (fun index => (output index).val) : ℝ) -
        PrimaryTensorInverse.tensorInverse security selected.card approximate output| +
      |PrimaryTensorInverse.tensorInverse security selected.card approximate output -
        PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security actualMass selected) output| :=
      abs_sub_le _ _ _
    _ ≤ _ := add_le_add hprogram hreal
    _ = _ := by unfold normalizedError; ring
open _root_.P2M9e1cfc64 renaming h169 → _p2mH169
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h172 (security bits : ℕ) (mass : (Fin 4 → ℕ) → ℚ)
    (selected : Finset (Fin 4)) (output : Fin selected.card → Palette security) :
    (selectedKernel security bits mass selected (fun index => (output index).val) : ℝ) =
      (FiniteDist.uniform (Equiv.Perm (Fin selected.card))).expectation (fun permutation =>
        (normalized security bits mass selected (fun index => (output (permutation index)).val) : ℝ)) := by
  simp only [selectedKernel, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_sum]
  unfold FiniteDist.expectation
  simp only [FiniteDist.uniform_weight, ← Finset.mul_sum, Fintype.card_perm, Fintype.card_fin, one_div]
  apply congrArg (fun value : ℝ => ((selected.card.factorial : ℝ)⁻¹) * value)
  apply Finset.sum_congr (by ext; simp)
  intro permutation _
  rfl
open _root_.P2M9e1cfc64 renaming h172 → _p2mH172
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h161 (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (output : Fin selected.card → Palette security)
    (body : Fin 0 → SafePalette security) :
    (LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output body =
      (FiniteDist.uniform (Equiv.Perm (Fin selected.card))).expectation (fun permutation =>
        PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security mass selected)
          (output ∘ permutation)) := by
  rw [_p2mH174, ControlProduct.symmetrize_apply]
  simp only [Fintype.card_perm, Fintype.card_fin, Nat.factorial_zero, Nat.cast_one, inv_one, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_mul]
  unfold FiniteDist.expectation
  simp only [FiniteDist.uniform_weight, ← Finset.mul_sum, Fintype.card_perm, Fintype.card_fin]
open _root_.P2M9e1cfc64 renaming h161 → _p2mH161
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h173 (security bits : ℕ) (mass : (Fin 4 → ℕ) → ℚ)
    (actualMass : (Fin 4 → Palette security) → ℝ) (selected : Finset (Fin 4))
    (massBound massError : ℝ) (hM : 0 ≤ massBound) (hE : 0 ≤ massError)
    (hmass : ∀ source, |actualMass source| ≤ massBound)
    (hdiff : ∀ source, |(mass (fun index => (source index).val) : ℝ) - actualMass source| ≤
      massError * (1 / (2 : ℝ)^bits))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) (body : Fin 0 → SafePalette security) :
    |(selectedKernel security bits mass selected (fun index => (output index).val) : ℝ) -
      (LocalCoefficientFamily.selectedKernel security selected.card actualMass selected (by simp)).val output body| ≤
        normalizedError security selected.card massBound massError * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH172, _p2mH161]
  unfold FiniteDist.expectation
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ permutation : Equiv.Perm (Fin selected.card),
        (FiniteDist.uniform (Equiv.Perm (Fin selected.card))).weight permutation *
          (normalizedError security selected.card massBound massError * (1 / (2 : ℝ)^bits)) := by
      apply Finset.sum_le_sum
      intro permutation _
      rw [← mul_sub, abs_mul, abs_of_nonneg (FiniteDist.nonneg _ _)]
      exact mul_le_mul_of_nonneg_left
        (_p2mH169 security bits mass actualMass selected massBound massError hM hE hmass hdiff
          hfirst hprecision hbudget (output ∘ permutation)) (FiniteDist.nonneg _ _)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
open _root_.P2M9e1cfc64 renaming h173 → _p2mH173
end
open _root_.P2M9e1cfc64 renaming h160 → _p2mH160
open _root_.P2M9e1cfc64 renaming h161 → _p2mH161
open _root_.P2M9e1cfc64 renaming h162 → _p2mH162
open _root_.P2M9e1cfc64 renaming h163 → _p2mH163
open _root_.P2M9e1cfc64 renaming h164 → _p2mH164
open _root_.P2M9e1cfc64 renaming h165 → _p2mH165
open _root_.P2M9e1cfc64 renaming h166 → _p2mH166
open _root_.P2M9e1cfc64 renaming h167 → _p2mH167
open _root_.P2M9e1cfc64 renaming h168 → _p2mH168
open _root_.P2M9e1cfc64 renaming h169 → _p2mH169
open _root_.P2M9e1cfc64 renaming h170 → _p2mH170
open _root_.P2M9e1cfc64 renaming h171 → _p2mH171
open _root_.P2M9e1cfc64 renaming h172 → _p2mH172
open _root_.P2M9e1cfc64 renaming h173 → _p2mH173
open _root_.P2M9e1cfc64 renaming h174 → _p2mH174
open _root_.P2M9e1cfc64 renaming h175 → _p2mH175
end CurrentAFT.RationalCoefficientExtraction
open _root_.P2M9e1cfc64 renaming h160 → _p2mH160
open _root_.P2M9e1cfc64 renaming h161 → _p2mH161
open _root_.P2M9e1cfc64 renaming h162 → _p2mH162
open _root_.P2M9e1cfc64 renaming h163 → _p2mH163
open _root_.P2M9e1cfc64 renaming h164 → _p2mH164
open _root_.P2M9e1cfc64 renaming h165 → _p2mH165
open _root_.P2M9e1cfc64 renaming h166 → _p2mH166
open _root_.P2M9e1cfc64 renaming h167 → _p2mH167
open _root_.P2M9e1cfc64 renaming h168 → _p2mH168
open _root_.P2M9e1cfc64 renaming h169 → _p2mH169
open _root_.P2M9e1cfc64 renaming h170 → _p2mH170
open _root_.P2M9e1cfc64 renaming h171 → _p2mH171
open _root_.P2M9e1cfc64 renaming h172 → _p2mH172
open _root_.P2M9e1cfc64 renaming h173 → _p2mH173
open _root_.P2M9e1cfc64 renaming h174 → _p2mH174
open _root_.P2M9e1cfc64 renaming h175 → _p2mH175
end
open _root_.P2M9e1cfc64 renaming h175 → _p2mH175
open _root_.P2M9e1cfc64 renaming h171 → _p2mH171
open _root_.P2M9e1cfc64 renaming h165 → _p2mH165
open _root_.P2M9e1cfc64 renaming h170 → _p2mH170
open _root_.P2M9e1cfc64 renaming h172 → _p2mH172
open _root_.P2M9e1cfc64 renaming h174 → _p2mH174
open _root_.P2M9e1cfc64 renaming h166 → _p2mH166
open _root_.P2M9e1cfc64 renaming h164 → _p2mH164
open _root_.P2M9e1cfc64 renaming h168 → _p2mH168
open _root_.P2M9e1cfc64 renaming h162 → _p2mH162
open _root_.P2M9e1cfc64 renaming h167 → _p2mH167
open _root_.P2M9e1cfc64 renaming h160 → _p2mH160
open _root_.P2M9e1cfc64 renaming h169 → _p2mH169
open _root_.P2M9e1cfc64 renaming h161 → _p2mH161
open _root_.P2M9e1cfc64 renaming h173 → _p2mH173
open _root_.P2M9e1cfc64 renaming h163 → _p2mH163
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
theorem _root_.P2M9e1cfc64.h375 (security bits : ℕ) (source color : Palette security) :
    (centerDelta security bits source.val color.val : ℝ) =
      (if color = source then (1 : ℝ) else 0) -
        (RationalProposalProgram.approximatePrimaryLaw security bits).weight source := by
  unfold centerDelta
  by_cases hequal : color = source
  · subst color
    simp only [if_true, Rat.cast_sub, Rat.cast_one]
    rfl
  · have hne : color.val ≠ source.val := fun h => hequal (Fin.ext h)
    simp only [if_neg hne, if_neg hequal, Rat.cast_sub, Rat.cast_zero]
    rfl
open _root_.P2M9e1cfc64 renaming h375 → _p2mH375
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h372 (security : ℕ) (source color : Palette security) :
    centerLinear (primaryLaw security) (Pi.single source 1) color =
      (if color = source then (1 : ℝ) else 0) - (primaryLaw security).weight source := by
  change (Pi.single (M := fun _ : Palette security => ℝ) source 1) color -
    (primaryLaw security).expectation (Pi.single source 1) = _
  simp [Pi.single_apply, FiniteDist.expectation]
open _root_.P2M9e1cfc64 renaming h372 → _p2mH372
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h374 (security bits : ℕ) (source color : Palette security) :
    |(centerDelta security bits source.val color.val : ℝ)| ≤ 1 := by
  rw [_p2mH375]
  have hlo := (RationalProposalProgram.approximatePrimaryLaw security bits).nonneg source
  have hhi := (RationalProposalProgram.approximatePrimaryLaw security bits).atom_le_one source
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2M9e1cfc64 renaming h374 → _p2mH374
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h373 (security : ℕ) (source color : Palette security) :
    |centerLinear (primaryLaw security) (Pi.single source 1) color| ≤ 1 := by
  rw [_p2mH372]
  have hlo := (primaryLaw security).nonneg source
  have hhi := (primaryLaw security).atom_le_one source
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2M9e1cfc64 renaming h373 → _p2mH373
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h376 (security bits : ℕ) (source color : Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(centerDelta security bits source.val color.val : ℝ) -
      centerLinear (primaryLaw security) (Pi.single source 1) color| ≤
        RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH375, _p2mH372]
  have h : |(RationalProposalProgram.approximatePrimaryLaw security bits).weight source -
      (primaryLaw security).weight source| ≤
      RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits) := by
    simpa only [RationalProposalProgram.approximatePrimaryLaw, primaryLaw, RationalRootMassProgram.primaryErrorConstant] using
      _p2mH392 security bits source hprecision hbudget
  have hequal : ((if color = source then (1 : ℝ) else 0) -
      (RationalProposalProgram.approximatePrimaryLaw security bits).weight source) -
      ((if color = source then (1 : ℝ) else 0) - (primaryLaw security).weight source) =
        (primaryLaw security).weight source - (RationalProposalProgram.approximatePrimaryLaw security bits).weight source := by ring
  rw [hequal, abs_sub_comm]
  exact h
open _root_.P2M9e1cfc64 renaming h376 → _p2mH376
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h379 (security : ℕ) (roots : RootTaggedSelected.RootPair security)
    (first second : Palette security → ℝ) (error : ℝ) (he : 0 ≤ error)
    (hdiff : ∀ color, |first color - second color| ≤ error) (word : Fin 4 → Palette security) :
    |RootMassColumns.primaryMassAt security roots first word - RootMassColumns.primaryMassAt security roots second word| ≤
      (2 * (Parameters.modulus security : ℝ)^2) * error := by
  change |(RootMassColumns.primaryMassAt security roots first - RootMassColumns.primaryMassAt security roots second) word| ≤ _
  rw [← map_sub]
  exact _p2mH414 security roots (first - second) error he hdiff word
open _root_.P2M9e1cfc64 renaming h379 → _p2mH379
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h378 (security bits : ℕ) (roots : RootTaggedSelected.RootPair security) (source : Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (word : Fin 4 → Palette security) :
    |(RationalRootMassProgram.primaryMass security bits roots.1.val roots.2.val
        (centerDelta security bits source.val) (fun index => (word index).val) : ℝ) -
      RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single source 1)) word| ≤
      massErrorConstant security * (1 / (2 : ℝ)^bits) := by
  let approximate := fun color : Palette security => (centerDelta security bits source.val color.val : ℝ)
  have hprogram := _p2mH416 security bits roots (centerDelta security bits source.val) 1
    (by norm_num) (_p2mH374 security bits source) hprecision hbudget word
  have hcentering := _p2mH379 security roots approximate
    (centerLinear (primaryLaw security) (Pi.single source 1))
    (RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits))
    (by unfold RationalRootMassProgram.primaryErrorConstant; positivity)
    (fun color => _p2mH376 security bits source color hprecision hbudget) word
  calc
    _ ≤ |(RationalRootMassProgram.primaryMass security bits roots.1.val roots.2.val
          (centerDelta security bits source.val) (fun index => (word index).val) : ℝ) -
        RootMassColumns.primaryMassAt security roots approximate word| +
      |RootMassColumns.primaryMassAt security roots approximate word -
        RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single source 1)) word| :=
      abs_sub_le _ _ _
    _ ≤ _ := add_le_add hprogram hcentering
    _ = _ := by unfold massErrorConstant; ring
open _root_.P2M9e1cfc64 renaming h378 → _p2mH378
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h377 (security bits : ℕ) (roots : RootTaggedSelected.RootPair security) (source : Palette security)
    (selected : Finset (Fin 4))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) (body : Fin 0 → SafePalette security) :
    |(current security bits roots.1.val roots.2.val source.val selected (fun index => (output index).val) : ℝ) -
      (LocalCoefficientFamily.selectedKernel security selected.card
        (RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single source 1)))
        selected (by simp)).val output body| ≤
      errorConstant security selected.card * (1 / (2 : ℝ)^bits) := by
  have hmassError : 0 ≤ massErrorConstant security := by
    unfold massErrorConstant RationalRootMassProgram.primaryMassErrorConstant RationalRootMassProgram.fixedErrorConstant
      RationalRootMassProgram.weightedErrorConstant RationalRootMassProgram.primaryErrorConstant
    positivity
  have h := _p2mH173 security bits
    (RationalRootMassProgram.primaryMass security bits roots.1.val roots.2.val (centerDelta security bits source.val))
    (RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single source 1))) selected
    (2 * (Parameters.modulus security : ℝ)^2) (massErrorConstant security) (by positivity) hmassError
    (fun word => by
      simpa only [mul_one] using _p2mH414 security roots
        (centerLinear (primaryLaw security) (Pi.single source 1)) 1 (by norm_num) (_p2mH373 security source) word)
    (fun word => _p2mH378 security bits roots source hprecision hbudget word)
    hfirst hprecision hbudget output body
  exact h
open _root_.P2M9e1cfc64 renaming h377 → _p2mH377
end
open _root_.P2M9e1cfc64 renaming h372 → _p2mH372
open _root_.P2M9e1cfc64 renaming h373 → _p2mH373
open _root_.P2M9e1cfc64 renaming h374 → _p2mH374
open _root_.P2M9e1cfc64 renaming h375 → _p2mH375
open _root_.P2M9e1cfc64 renaming h376 → _p2mH376
open _root_.P2M9e1cfc64 renaming h377 → _p2mH377
open _root_.P2M9e1cfc64 renaming h378 → _p2mH378
open _root_.P2M9e1cfc64 renaming h379 → _p2mH379
end CurrentAFT.RationalPrimaryColumnProgram
open _root_.P2M9e1cfc64 renaming h372 → _p2mH372
open _root_.P2M9e1cfc64 renaming h373 → _p2mH373
open _root_.P2M9e1cfc64 renaming h374 → _p2mH374
open _root_.P2M9e1cfc64 renaming h375 → _p2mH375
open _root_.P2M9e1cfc64 renaming h376 → _p2mH376
open _root_.P2M9e1cfc64 renaming h377 → _p2mH377
open _root_.P2M9e1cfc64 renaming h378 → _p2mH378
open _root_.P2M9e1cfc64 renaming h379 → _p2mH379
end
open _root_.P2M9e1cfc64 renaming h376 → _p2mH376
open _root_.P2M9e1cfc64 renaming h379 → _p2mH379
open _root_.P2M9e1cfc64 renaming h373 → _p2mH373
open _root_.P2M9e1cfc64 renaming h378 → _p2mH378
open _root_.P2M9e1cfc64 renaming h375 → _p2mH375
open _root_.P2M9e1cfc64 renaming h372 → _p2mH372
open _root_.P2M9e1cfc64 renaming h377 → _p2mH377
open _root_.P2M9e1cfc64 renaming h374 → _p2mH374
section
namespace CurrentAFT.RationalLocalFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalLocalFamilyProgram.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalLocalFamilyProgram.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h263 (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    insertSelected order selected
      (fun word => (LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val word Fin.elim0)
        arity colors centers =
      (LocalCoefficientFamily.selectedFamily security order mass selected arity).val colors centers := by
  unfold insertSelected LocalCoefficientFamily.selectedFamily
  by_cases hdegree : selected.card ≤ order
  · rw [dif_pos hdegree]
    by_cases hmatch : selected.card = arity.val.1.val ∧ 0 = arity.val.2.val
    · have harity : arity = LocalCoefficientFamily.selectedArity order selected hdegree := by
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          exact hmatch.1.symm
        · apply Fin.ext
          exact hmatch.2.symm
      subst arity
      rw [dif_pos hmatch, Pi.single_eq_same]
      have hcenters : centers = (Fin.elim0 : Fin 0 → SafePalette security) :=
        @Subsingleton.elim (Fin 0 → SafePalette security) inferInstance centers Fin.elim0
      rw [hcenters]
      rfl
    · have harity : arity ≠ LocalCoefficientFamily.selectedArity order selected hdegree := by
        intro hequal
        apply hmatch
        subst arity
        exact ⟨rfl, rfl⟩
      rw [dif_neg hmatch]
      have hzero := Pi.single_eq_of_ne
        (M := fun point : TruncatedArity order =>
          canonicalKernels (primaryLaw security) (bodyReference security) point.val.1.val point.val.2.val) harity
        (LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp))
      rw [hzero]
      rfl
  · rw [dif_neg hdegree]
    have hmatch : ¬(selected.card = arity.val.1.val ∧ 0 = arity.val.2.val) := by
      intro h
      have hbound := arity.property
      omega
    rw [dif_neg hmatch]
    rfl
open _root_.P2M9e1cfc64 renaming h263 → _p2mH263
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h262 (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (hmass : ∑ word, mass word = 0) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    (LocalRaisingLinear.completeFamilyLinear security order mass arity).val colors centers =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        insertSelected order selected
          (fun word => (LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val word Fin.elim0)
          arity colors centers := by
  change (NormalizedLocalPolynomial.completeFamily security order mass arity).val colors centers = _
  unfold NormalizedLocalPolynomial.completeFamily
  rw [hmass, zero_smul, zero_add]
  simp only [Finset.sum_apply, Submodule.coe_sum]
  apply Finset.sum_congr (by ext; simp)
  intro selected _
  exact (_p2mH263 security order mass selected arity colors centers).symm
open _root_.P2M9e1cfc64 renaming h262 → _p2mH262
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h267 (security : ℕ) (roots : RootTaggedSelected.RootPair security) (primaryColor : Palette security) :
    (∑ word, RootMassColumns.primaryMassAt security roots
      (centerLinear (primaryLaw security) (Pi.single primaryColor 1)) word) = 0 := by
  simp only [_p2mH413]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro scalar _
  rw [← Finset.mul_sum, FixedPairedFirst.fixedMass_sum, center_mean, mul_zero, mul_zero]
open _root_.P2M9e1cfc64 renaming h267 → _p2mH267
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h266 (security degree : ℕ) :
    0 ≤ RationalPrimaryColumnProgram.errorConstant security degree := by
  unfold RationalPrimaryColumnProgram.errorConstant RationalPrimaryColumnProgram.massErrorConstant
    RationalCoefficientExtraction.normalizedError RationalCoefficientExtraction.extractionBound
    RationalCoefficientExtraction.extractionError RationalCoefficientExtraction.atomErrorConstant
    RationalRootMassProgram.primaryMassErrorConstant RationalRootMassProgram.fixedErrorConstant
    RationalRootMassProgram.weightedErrorConstant RationalRootMassProgram.primaryErrorConstant
    RationalTensorInverseProgram.tensorErrorConstant
  positivity [_p2mH455 security,
    _p2mH462 security, _p2mH463 security]
open _root_.P2M9e1cfc64 renaming h266 → _p2mH266
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h264 (order : ℕ) (selected : Finset (Fin 4)) (security : ℕ)
    (computed : (Fin selected.card → ℕ) → ℚ) (actual : (Fin selected.card → Palette security) → ℝ)
    (error : ℝ) (he : 0 ≤ error)
    (hvalue : ∀ word, |(computed (fun index => (word index).val) : ℝ) - actual word| ≤ error)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(insertSelected order selected computed arity (fun index => (colors index).val)
        (fun index => (centers index).val.val) : ℝ) -
      insertSelected order selected actual arity colors centers| ≤ error := by
  unfold insertSelected
  split_ifs with hmatch
  · exact hvalue (colors ∘ finCongr hmatch.1)
  · simpa only [Rat.cast_zero, sub_self, abs_zero] using he
open _root_.P2M9e1cfc64 renaming h264 → _p2mH264
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h265 (security bits order : ℕ) (roots : RootTaggedSelected.RootPair security)
    (primaryColor : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(numerator security bits order roots.1.val roots.2.val primaryColor.val arity
        (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (LocalRaisingLinear.completeFamilyLinear security order
        (RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single primaryColor 1)))
          arity).val colors centers| ≤
      numeratorErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have hsum : (numerator security bits order roots.1.val roots.2.val primaryColor.val arity
      (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
      (insertSelected order selected
        (RationalPrimaryColumnProgram.current security bits roots.1.val roots.2.val primaryColor.val selected)
        arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) := by
    unfold numerator
    simp only [Rat.cast_sum]
    apply Finset.sum_congr (by ext; simp)
    intro selected _
    rfl
  rw [hsum, _p2mH262 security order _ (_p2mH267 security roots primaryColor)]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        RationalPrimaryColumnProgram.errorConstant security selected.card * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro selected _
      exact _p2mH264 order selected security _ _ _ (by positivity [_p2mH266 security selected.card])
        (fun word => _p2mH377 security bits roots primaryColor selected hfirst hprecision hbudget
          word Fin.elim0) arity colors centers
    _ = _ := by rw [← Finset.sum_mul]; rfl
open _root_.P2M9e1cfc64 renaming h265 → _p2mH265
end
open _root_.P2M9e1cfc64 renaming h262 → _p2mH262
open _root_.P2M9e1cfc64 renaming h263 → _p2mH263
open _root_.P2M9e1cfc64 renaming h264 → _p2mH264
open _root_.P2M9e1cfc64 renaming h265 → _p2mH265
open _root_.P2M9e1cfc64 renaming h266 → _p2mH266
open _root_.P2M9e1cfc64 renaming h267 → _p2mH267
end CurrentAFT.RationalLocalFamilyProgram
open _root_.P2M9e1cfc64 renaming h262 → _p2mH262
open _root_.P2M9e1cfc64 renaming h263 → _p2mH263
open _root_.P2M9e1cfc64 renaming h264 → _p2mH264
open _root_.P2M9e1cfc64 renaming h265 → _p2mH265
open _root_.P2M9e1cfc64 renaming h266 → _p2mH266
open _root_.P2M9e1cfc64 renaming h267 → _p2mH267
end
open _root_.P2M9e1cfc64 renaming h263 → _p2mH263
open _root_.P2M9e1cfc64 renaming h267 → _p2mH267
open _root_.P2M9e1cfc64 renaming h266 → _p2mH266
open _root_.P2M9e1cfc64 renaming h265 → _p2mH265
open _root_.P2M9e1cfc64 renaming h264 → _p2mH264
open _root_.P2M9e1cfc64 renaming h262 → _p2mH262
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h209 {Primary Body : Type*} (order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Primary) (centers : Fin arity.val.2.val → Body) :
    |unit (Scalar := ℝ) order arity colors centers| ≤ 1 := by
  unfold unit
  split_ifs <;> norm_num
open _root_.P2M9e1cfc64 renaming h209 → _p2mH209
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h192 {Primary Body : Type*} (order : ℕ) (table : Table ℝ Primary Body order)
    (bound scale : ℝ) (hb : 0 ≤ bound) (hs : 1 ≤ scale)
    (hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * bound ≤ scale)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound) (count : ℕ)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |power order table count arity colors centers| ≤ scale^count := by
  induction count generalizing arity colors centers with
  | zero => simpa only [power, pow_zero] using _p2mH209 order arity colors centers
  | succ count ih =>
      have h := _p2mH196 order (power order table count) table (scale^count) bound
        (pow_nonneg (by linarith) _) hb ih htable arity colors centers
      simp only [Fintype.card_eq_nat_card] at h
      apply h.trans
      have hm := mul_le_mul_of_nonneg_left hscale (pow_nonneg (by linarith : 0 ≤ scale) count)
      rw [pow_succ scale count]
      convert hm using 1
      ring
open _root_.P2M9e1cfc64 renaming h192 → _p2mH192
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h184 (order : ℕ) (bound error : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) :
    1 ≤ growth order bound error := by
  unfold growth
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (by positivity))
open _root_.P2M9e1cfc64 renaming h184 → _p2mH184
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h185 (order : ℕ) (bound error : ℝ) :
    (Nat.card (TruncatedArity order) : ℝ)^2 * (bound + error + 1) ≤ growth order bound error := by
  unfold growth
  linarith
open _root_.P2M9e1cfc64 renaming h185 → _p2mH185
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h194 {Primary Body : Type*} (order : ℕ) (table computed : Table ℝ Primary Body order)
    (bound error scale : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hs : 1 ≤ scale)
    (hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * (bound + error + 1) ≤ scale)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound)
    (herror : ∀ arity colors centers, |computed arity colors centers - table arity colors centers| ≤ error)
    (count : ℕ) (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |power order computed count arity colors centers - power order table count arity colors centers| ≤
      count * error * scale^count := by
  have hn : 0 ≤ (Nat.card (TruncatedArity order) : ℝ)^2 := sq_nonneg _
  have hbase : (Nat.card (TruncatedArity order) : ℝ)^2 * bound ≤ scale :=
    (mul_le_mul_of_nonneg_left (show bound ≤ bound+error+1 by linarith) hn).trans hscale
  have hstep : (Nat.card (TruncatedArity order) : ℝ)^2 * (bound+error) ≤ scale :=
    (mul_le_mul_of_nonneg_left (show bound+error ≤ bound+error+1 by linarith) hn).trans hscale
  have hcount : (Nat.card (TruncatedArity order) : ℝ)^2 ≤ scale := by
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ bound+error+1 by linarith) hn
    rw [mul_one] at h
    exact h.trans hscale
  induction count generalizing arity colors centers with
  | zero => simp only [power, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ count ih =>
      have hp := _p2mH192 order table bound scale hb hs hbase htable count
      have h := _p2mH198 order (power order table count) (power order computed count) table computed
        (scale^count) bound (count*error*scale^count) error
        (by positivity) hb (by positivity) he hp htable ih herror arity colors centers
      simp only [Fintype.card_eq_nat_card] at h
      apply h.trans
      have hfirst := mul_le_mul_of_nonneg_left hstep
        (show 0 ≤ (count:ℝ)*error*scale^count by positivity)
      have hsecond := mul_le_mul_of_nonneg_left hcount (show 0 ≤ error*scale^count by positivity)
      calc
        _ = ((count:ℝ)*error*scale^count) *
            ((Nat.card (TruncatedArity order):ℝ)^2*(bound+error)) +
            (error*scale^count) * (Nat.card (TruncatedArity order):ℝ)^2 := by ring
        _ ≤ ((count:ℝ)*error*scale^count)*scale + (error*scale^count)*scale := add_le_add hfirst hsecond
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one, pow_succ]; ring
open _root_.P2M9e1cfc64 renaming h194 → _p2mH194
end
open _root_.P2M9e1cfc64 renaming h184 → _p2mH184
open _root_.P2M9e1cfc64 renaming h185 → _p2mH185
open _root_.P2M9e1cfc64 renaming h192 → _p2mH192
open _root_.P2M9e1cfc64 renaming h194 → _p2mH194
open _root_.P2M9e1cfc64 renaming h209 → _p2mH209
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M9e1cfc64 renaming h184 → _p2mH184
open _root_.P2M9e1cfc64 renaming h185 → _p2mH185
open _root_.P2M9e1cfc64 renaming h192 → _p2mH192
open _root_.P2M9e1cfc64 renaming h194 → _p2mH194
open _root_.P2M9e1cfc64 renaming h209 → _p2mH209
end
open _root_.P2M9e1cfc64 renaming h185 → _p2mH185
open _root_.P2M9e1cfc64 renaming h192 → _p2mH192
open _root_.P2M9e1cfc64 renaming h194 → _p2mH194
open _root_.P2M9e1cfc64 renaming h209 → _p2mH209
open _root_.P2M9e1cfc64 renaming h184 → _p2mH184
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h205 {Primary Body : Type*} (order : ℕ) (table : Table ℝ Primary Body order)
    (bound : ℝ) (hb : 0 ≤ bound)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |reciprocal order table arity colors centers| ≤
      ((order+1 : ℕ):ℝ) * (growth order (1+bound) 0)^order := by
  let scale := growth order (1+bound) 0
  have hs : 1 ≤ scale := _p2mH184 order (1+bound) 0 (by positivity) (by norm_num)
  have htable' (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
      (centers : Fin arity.val.2.val → Body) :
      |(unit order - table : Table ℝ Primary Body order) arity colors centers| ≤ 1+bound :=
    (abs_sub _ _).trans (add_le_add (_p2mH209 order arity colors centers) (htable arity colors centers))
  have hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * (1+bound) ≤ scale := by
    dsimp [scale, growth]
    nlinarith [sq_nonneg (Nat.card (TruncatedArity order) : ℝ)]
  unfold reciprocal
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _count ∈ Finset.range (order+1), scale^order := by
      apply Finset.sum_le_sum
      intro count hcount
      exact (_p2mH192 order (unit order - table) (1+bound) scale (by positivity) hs hscale
        htable' count arity colors centers).trans (pow_le_pow_right₀ hs (by
          have := Finset.mem_range.mp hcount; omega))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; rfl
open _root_.P2M9e1cfc64 renaming h205 → _p2mH205
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h207 {Primary Body : Type*} (order : ℕ) (table computed : Table ℝ Primary Body order)
    (bound error : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound)
    (herror : ∀ arity colors centers, |computed arity colors centers - table arity colors centers| ≤ error)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |reciprocal order computed arity colors centers - reciprocal order table arity colors centers| ≤
      ((order+1 : ℕ):ℝ)^2 * error * (growth order (1+bound) error)^(order+1) := by
  let scale := growth order (1+bound) error
  have hs : 1 ≤ scale := _p2mH184 order (1+bound) error (by positivity) he
  have htable' (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
      (centers : Fin arity.val.2.val → Body) : |(unit order - table : Table ℝ Primary Body order) arity colors centers| ≤ 1+bound :=
    (abs_sub _ _).trans (add_le_add (_p2mH209 order arity colors centers) (htable arity colors centers))
  have herror' (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
      (centers : Fin arity.val.2.val → Body) :
      |(unit order - computed : Table ℝ Primary Body order) arity colors centers - (unit order - table : Table ℝ Primary Body order) arity colors centers| ≤ error := by
    change |(unit order arity colors centers - computed arity colors centers) -
      (unit order arity colors centers - table arity colors centers)| ≤ error
    rw [sub_sub_sub_cancel_left, abs_sub_comm]
    exact herror arity colors centers
  unfold reciprocal
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _count ∈ Finset.range (order+1), ((order+1 : ℕ):ℝ)*error*scale^(order+1) := by
      apply Finset.sum_le_sum
      intro count hcount
      have hc : count ≤ order+1 := by have := Finset.mem_range.mp hcount; omega
      have h := _p2mH194 order (unit order - table : Table ℝ Primary Body order) (unit order - computed : Table ℝ Primary Body order)
        (1+bound) error scale (by positivity) he hs (_p2mH185 order (1+bound) error)
        htable' herror' count arity colors centers
      apply h.trans
      apply mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) he)
        (pow_le_pow_right₀ hs hc) (by positivity) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; dsimp only [scale]; ring
open _root_.P2M9e1cfc64 renaming h207 → _p2mH207
end
open _root_.P2M9e1cfc64 renaming h205 → _p2mH205
open _root_.P2M9e1cfc64 renaming h207 → _p2mH207
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M9e1cfc64 renaming h205 → _p2mH205
open _root_.P2M9e1cfc64 renaming h207 → _p2mH207
end
open _root_.P2M9e1cfc64 renaming h207 → _p2mH207
open _root_.P2M9e1cfc64 renaming h205 → _p2mH205
section
namespace CurrentAFT.RationalPositiveFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalPositiveFamilyProgram.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPositiveFamilyProgram.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h361 (security : ℕ) : 0 ≤ RationalPositiveReferenceProgram.errorConstant security := by
  unfold RationalPositiveReferenceProgram.errorConstant RationalPositiveReferenceProgram.fixedErrorConstant
    RationalRootMassProgram.primaryErrorConstant
  positivity
open _root_.P2M9e1cfc64 renaming h361 → _p2mH361
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h359 (security degree : ℕ) : 0 ≤ coefficientError security degree := by
  unfold coefficientError RationalCoefficientExtraction.normalizedError RationalCoefficientExtraction.extractionBound
    RationalCoefficientExtraction.extractionError RationalCoefficientExtraction.atomErrorConstant
    RationalRootMassProgram.primaryErrorConstant RationalTensorInverseProgram.tensorErrorConstant
  positivity [_p2mH361 security, _p2mH455 security,
    _p2mH462 security, _p2mH463 security]
open _root_.P2M9e1cfc64 renaming h359 → _p2mH359
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h360 (security bits : ℕ) (selected : Finset (Fin 4))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) (centers : Fin 0 → SafePalette security) :
    |(coefficient security bits selected (fun index => (output index).val) : ℝ) -
      (LocalCoefficientFamily.selectedKernel security selected.card
        (NormalizedLocalPolynomial.independentPositiveLaw security).weight selected (by simp)).val output centers| ≤
      coefficientError security selected.card * (1 / (2 : ℝ)^bits) := by
  exact _p2mH173 security bits
    (RationalPositiveReferenceProgram.current security bits) (NormalizedLocalPolynomial.independentPositiveLaw security).weight
    selected 1 (RationalPositiveReferenceProgram.errorConstant security) (by norm_num) (_p2mH361 security)
    (fun word => by
      rw [abs_of_nonneg ((NormalizedLocalPolynomial.independentPositiveLaw security).nonneg word)]
      exact (NormalizedLocalPolynomial.independentPositiveLaw security).atom_le_one word)
    (fun word => _p2mH368 security bits hprecision hbudget word)
    hfirst hprecision hbudget output centers
open _root_.P2M9e1cfc64 renaming h360 → _p2mH360
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h364 (order security : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    ((unit order arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℚ) : ℝ) =
      unit order arity colors centers := by
  unfold unit
  split_ifs <;> norm_num
open _root_.P2M9e1cfc64 renaming h364 → _p2mH364
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h362 (security order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    (NormalizedLocalPolynomial.positiveFamily security order (NormalizedLocalPolynomial.independentPositiveLaw security) arity).val
      colors centers = unit order arity colors centers +
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        RationalLocalFamilyProgram.insertSelected order selected
          (fun word => (LocalCoefficientFamily.selectedKernel security selected.card
            (NormalizedLocalPolynomial.independentPositiveLaw security).weight selected (by simp)).val word Fin.elim0)
          arity colors centers := by
  unfold NormalizedLocalPolynomial.positiveFamily NormalizedLocalPolynomial.completeFamily
  rw [FiniteDist.sum_one, one_smul]
  simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_apply, Submodule.coe_sum]
  have hunit := congrFun (congrFun (congrFun (_p2mH208 (primaryLaw security) (bodyReference security) order) arity) colors) centers
  rw [← hunit]
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro selected _
  exact (_p2mH263 security order _ selected arity colors centers).symm
open _root_.P2M9e1cfc64 renaming h362 → _p2mH362
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h363 (security bits order : ℕ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(positive security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (NormalizedLocalPolynomial.positiveFamily security order (NormalizedLocalPolynomial.independentPositiveLaw security) arity).val
        colors centers| ≤ errorConstant security * (1 / (2 : ℝ)^bits) := by
  have hsum : (positive security bits order arity (fun index => (colors index).val)
      (fun index => (centers index).val.val) : ℝ) = unit order arity colors centers +
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        (RationalLocalFamilyProgram.insertSelected order selected (coefficient security bits selected)
          arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) := by
    unfold positive
    simp only [Rat.cast_add, Rat.cast_sum]
    have hu : ((unit order arity (fun index => (colors index).val)
        (fun index => (centers index).val.val) : ℚ) : ℝ) = unit order arity colors centers := by
      unfold unit
      split_ifs <;> norm_num
    rw [hu]
    congr 1
  rw [hsum, _p2mH362, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        coefficientError security selected.card * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro selected _
      exact _p2mH264 order selected security _ _ _
        (by positivity [_p2mH359 security selected.card])
        (fun word => _p2mH360 security bits selected hfirst hprecision hbudget word Fin.elim0)
        arity colors centers
    _ = _ := by rw [← Finset.sum_mul]; rfl
open _root_.P2M9e1cfc64 renaming h363 → _p2mH363
end
open _root_.P2M9e1cfc64 renaming h359 → _p2mH359
open _root_.P2M9e1cfc64 renaming h360 → _p2mH360
open _root_.P2M9e1cfc64 renaming h361 → _p2mH361
open _root_.P2M9e1cfc64 renaming h362 → _p2mH362
open _root_.P2M9e1cfc64 renaming h363 → _p2mH363
open _root_.P2M9e1cfc64 renaming h364 → _p2mH364
end CurrentAFT.RationalPositiveFamilyProgram
open _root_.P2M9e1cfc64 renaming h359 → _p2mH359
open _root_.P2M9e1cfc64 renaming h360 → _p2mH360
open _root_.P2M9e1cfc64 renaming h361 → _p2mH361
open _root_.P2M9e1cfc64 renaming h362 → _p2mH362
open _root_.P2M9e1cfc64 renaming h363 → _p2mH363
open _root_.P2M9e1cfc64 renaming h364 → _p2mH364
end
open _root_.P2M9e1cfc64 renaming h362 → _p2mH362
open _root_.P2M9e1cfc64 renaming h363 → _p2mH363
open _root_.P2M9e1cfc64 renaming h360 → _p2mH360
open _root_.P2M9e1cfc64 renaming h364 → _p2mH364
open _root_.P2M9e1cfc64 renaming h359 → _p2mH359
open _root_.P2M9e1cfc64 renaming h361 → _p2mH361
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
variable {Scalar Primary Body Primary' Body' : Type*}
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h203 [Zero Scalar] [One Scalar] (order : ℕ)
    (primary : Primary' → Primary) (body : Body' → Body) :
    pullback order primary body (unit (Scalar := Scalar) order) = unit order := rfl
open _root_.P2M9e1cfc64 renaming h203 → _p2mH203
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h202 [Sub Scalar] (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
    (first second : Table Scalar Primary Body order) :
    pullback order primary body (first - second) = pullback order primary body first - pullback order primary body second := rfl
open _root_.P2M9e1cfc64 renaming h202 → _p2mH202
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h200 [Field Scalar] (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
    (first second : Table Scalar Primary Body order) :
    pullback order primary body (product order first second) =
      product order (pullback order primary body first) (pullback order primary body second) := by
  funext arity colors centers
  unfold pullback product
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  split_ifs <;> rfl
open _root_.P2M9e1cfc64 renaming h200 → _p2mH200
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h199 [Field Scalar] (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
    (table : Table Scalar Primary Body order) (count : ℕ) :
    pullback order primary body (power order table count) =
      power order (pullback order primary body table) count := by
  induction count with
  | zero => exact _p2mH203 order primary body
  | succ count ih => simp only [power, _p2mH200, ih]
open _root_.P2M9e1cfc64 renaming h199 → _p2mH199
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h201 [Field Scalar] (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
    (table : Table Scalar Primary Body order) :
    pullback order primary body (reciprocal order table) = reciprocal order (pullback order primary body table) := by
  funext arity colors centers
  unfold reciprocal
  change (∑ count ∈ Finset.range (order+1),
    pullback order primary body (power order (unit order-table) count) arity colors centers) = _
  simp only [_p2mH199, _p2mH202, _p2mH203]
open _root_.P2M9e1cfc64 renaming h201 → _p2mH201
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M9e1cfc64 renaming h199 → _p2mH199
open _root_.P2M9e1cfc64 renaming h200 → _p2mH200
open _root_.P2M9e1cfc64 renaming h201 → _p2mH201
open _root_.P2M9e1cfc64 renaming h202 → _p2mH202
open _root_.P2M9e1cfc64 renaming h203 → _p2mH203
end
open _root_.P2M9e1cfc64 renaming h200 → _p2mH200
open _root_.P2M9e1cfc64 renaming h199 → _p2mH199
open _root_.P2M9e1cfc64 renaming h203 → _p2mH203
open _root_.P2M9e1cfc64 renaming h202 → _p2mH202
open _root_.P2M9e1cfc64 renaming h201 → _p2mH201
section
namespace CurrentAFT.PositiveFamilyPointBound
open AFT ProposalPrimary ActualControls LocalCoefficientFamily NormalizedLocalPolynomial
  LocalRaisingBounds GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.PositiveFamilyPointBound.classicalFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h141 (security order : ℕ) :
    coefficientNorm security order (positiveFamily security order (independentPositiveLaw security)) ≤
      1 + positiveConstant := by
  have hadd := familyNorm_add_le (primaryLaw security) (bodyReference security) order
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (RaisingPatternBudget.primaryFactor_pos security).le (RaisingPatternBudget.bodyFactor_pos security).le
    (positiveFamily security order (independentPositiveLaw security) - 1) 1
  rw [sub_add_cancel, familyNorm_one] at hadd
  have hbase : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hden : (1 : ℝ) ≤ (Parameters.base security : ℝ)^39 := one_le_pow₀ hbase
  have hd := (independentPositive_defect security order).trans
    (div_le_self positiveConstant_nonneg hden)
  change coefficientNorm security order _ ≤ coefficientNorm security order _ + 1 at hadd
  linarith
open _root_.P2M9e1cfc64 renaming h141 → _p2mH141
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h142 (security order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → ActualControls.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |((positiveFamily security order (independentPositiveLaw security)) arity).val colors centers| ≤ bound security order :=
  (_p2mH29 security order _ arity colors centers).trans
    (mul_le_mul_of_nonneg_left (_p2mH141 security order) (by positivity))
open _root_.P2M9e1cfc64 renaming h142 → _p2mH142
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h140 (security order : ℕ) : 0 ≤ bound security order := by
  unfold bound
  positivity [positiveConstant_nonneg]
open _root_.P2M9e1cfc64 renaming h140 → _p2mH140
end
open _root_.P2M9e1cfc64 renaming h140 → _p2mH140
open _root_.P2M9e1cfc64 renaming h141 → _p2mH141
open _root_.P2M9e1cfc64 renaming h142 → _p2mH142
end CurrentAFT.PositiveFamilyPointBound
open _root_.P2M9e1cfc64 renaming h140 → _p2mH140
open _root_.P2M9e1cfc64 renaming h141 → _p2mH141
open _root_.P2M9e1cfc64 renaming h142 → _p2mH142
end
open _root_.P2M9e1cfc64 renaming h141 → _p2mH141
open _root_.P2M9e1cfc64 renaming h142 → _p2mH142
open _root_.P2M9e1cfc64 renaming h140 → _p2mH140
section
namespace CurrentAFT.LocalCoefficientPointBounds
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.LocalCoefficientPointBounds.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.LocalCoefficientPointBounds.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h108 (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → Palette security) :
    |RationalCoefficientExtraction.orderedDensity security mass selected output| ≤
      (Parameters.modulus security : ℝ)^4 * bound * (4 * (Parameters.modulus security : ℝ))^selected.card := by
  unfold RationalCoefficientExtraction.orderedDensity LocalTensors.referenceRestrictedComponent
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _word : Fin 4 → Palette security, bound * (4 * (Parameters.modulus security : ℝ))^selected.card := by
      apply Finset.sum_le_sum
      intro word _
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul (hmass word) _ (Finset.prod_nonneg fun _ _ => abs_nonneg _) hb
      calc
        _ ≤ ∏ _slot : selected, 4 * (Parameters.modulus security : ℝ) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun slot _ => _p2mH160 security _ _)
        _ = _ := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
open _root_.P2M9e1cfc64 renaming h108 → _p2mH108
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h112 (security degree : ℕ) (profile : (Fin degree → Palette security) → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hprofile : ∀ word, |profile word| ≤ bound)
    (output : Fin degree → Palette security) :
    |PrimaryTensorInverse.tensorInverse security degree profile output| ≤
      (Parameters.modulus security : ℝ)^degree * (RationalTensorInverseProgram.actualBound security)^degree * bound := by
  have h := _p2mH457 security degree profile 0 bound hb
    (fun word => by simpa only [Pi.zero_apply, sub_zero] using hprofile word) output
  simpa only [map_zero, Pi.zero_apply, sub_zero] using h
open _root_.P2M9e1cfc64 renaming h112 → _p2mH112
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h110 (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → Palette security) (centers : Fin 0 → SafePalette security) :
    |(LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output centers| ≤
      (Parameters.modulus security : ℝ)^selected.card * (RationalTensorInverseProgram.actualBound security)^selected.card *
        ((Parameters.modulus security : ℝ)^4 * bound * (4 * (Parameters.modulus security : ℝ))^selected.card) := by
  rw [_p2mH161]
  apply _p2mH48
  intro permutation
  exact _p2mH112 security selected.card _ _ (by positivity) (_p2mH108 security mass selected bound hb hmass)
    (output ∘ permutation)
open _root_.P2M9e1cfc64 renaming h110 → _p2mH110
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h109 (security : ℕ) (bound : ℝ) (hb : 0 ≤ bound) : 0 ≤ selectedBound security bound := by
  unfold selectedBound
  positivity [_p2mH455 security]
open _root_.P2M9e1cfc64 renaming h109 → _p2mH109
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h111 (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → Palette security) (centers : Fin 0 → SafePalette security) :
    |(LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output centers| ≤
      selectedBound security bound := by
  have hcard : selected.card ≤ 4 := (Finset.card_le_card (Finset.subset_univ selected)).trans_eq (by simp)
  have hq : (1 : ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_spec security).2.two_le.trans' (by omega)
  have hM := _p2mH455 security
  have hqpow := pow_le_pow_right₀ hq hcard
  have hfour : (1 : ℝ) ≤ 4 * (Parameters.modulus security : ℝ) := by linarith
  have hfourpow := pow_le_pow_right₀ hfour hcard
  have hMpow : (RationalTensorInverseProgram.actualBound security)^selected.card ≤
      (1 + RationalTensorInverseProgram.actualBound security)^4 :=
    (pow_le_pow_left₀ hM (show RationalTensorInverseProgram.actualBound security ≤
        1 + RationalTensorInverseProgram.actualBound security by linarith) selected.card).trans
      (pow_le_pow_right₀ (by linarith) hcard)
  apply (_p2mH110 security mass selected bound hb hmass output centers).trans
  exact mul_le_mul (mul_le_mul hqpow hMpow (pow_nonneg hM _) (by positivity))
    (mul_le_mul_of_nonneg_left hfourpow (by positivity)) (by positivity) (by positivity)
open _root_.P2M9e1cfc64 renaming h111 → _p2mH111
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h106 (security : ℕ) : 0 ≤ numeratorBound security :=
  mul_nonneg (by norm_num) (_p2mH109 security _ (by positivity))
open _root_.P2M9e1cfc64 renaming h106 → _p2mH106
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h107 (security order : ℕ) (roots : RootTaggedSelected.RootPair security)
    (primaryColor : Palette security) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    |(LocalRaisingLinear.completeFamilyLinear security order
        (RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single primaryColor 1)))
          arity).val colors centers| ≤ numeratorBound security := by
  rw [_p2mH262 security order _
    (_p2mH267 security roots primaryColor)]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        selectedBound security (2 * (Parameters.modulus security : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro selected _
      unfold RationalLocalFamilyProgram.insertSelected
      split_ifs with hmatch
      · exact _p2mH111 security _ selected _ (by positivity)
          (fun word => by
            simpa only [mul_one] using _p2mH414 security roots
              (centerLinear (primaryLaw security) (Pi.single primaryColor 1)) 1 (by norm_num)
              (_p2mH373 security primaryColor) word)
          (colors ∘ finCongr hmatch.1) Fin.elim0
      · simpa only [abs_zero] using _p2mH109 security (2 * (Parameters.modulus security : ℝ)^2) (by positivity)
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (_p2mH109 security _ (by positivity))
      apply Nat.cast_le.mpr
      calc
        _ ≤ (Finset.univ : Finset (Finset (Fin 4))).card := Finset.card_le_card (Finset.erase_subset ..)
        _ = 16 := by norm_num
open _root_.P2M9e1cfc64 renaming h107 → _p2mH107
end
open _root_.P2M9e1cfc64 renaming h106 → _p2mH106
open _root_.P2M9e1cfc64 renaming h107 → _p2mH107
open _root_.P2M9e1cfc64 renaming h108 → _p2mH108
open _root_.P2M9e1cfc64 renaming h109 → _p2mH109
open _root_.P2M9e1cfc64 renaming h110 → _p2mH110
open _root_.P2M9e1cfc64 renaming h111 → _p2mH111
open _root_.P2M9e1cfc64 renaming h112 → _p2mH112
end CurrentAFT.LocalCoefficientPointBounds
open _root_.P2M9e1cfc64 renaming h106 → _p2mH106
open _root_.P2M9e1cfc64 renaming h107 → _p2mH107
open _root_.P2M9e1cfc64 renaming h108 → _p2mH108
open _root_.P2M9e1cfc64 renaming h109 → _p2mH109
open _root_.P2M9e1cfc64 renaming h110 → _p2mH110
open _root_.P2M9e1cfc64 renaming h111 → _p2mH111
open _root_.P2M9e1cfc64 renaming h112 → _p2mH112
end
open _root_.P2M9e1cfc64 renaming h108 → _p2mH108
open _root_.P2M9e1cfc64 renaming h106 → _p2mH106
open _root_.P2M9e1cfc64 renaming h107 → _p2mH107
open _root_.P2M9e1cfc64 renaming h111 → _p2mH111
open _root_.P2M9e1cfc64 renaming h109 → _p2mH109
open _root_.P2M9e1cfc64 renaming h112 → _p2mH112
open _root_.P2M9e1cfc64 renaming h110 → _p2mH110
section
namespace CurrentAFT.RationalNormalizedPrimaryProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalNormalizedPrimaryProgram.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalNormalizedPrimaryProgram.classicalSubtypeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h284 (security bits order : ℕ) :
    lifted security order (RationalPositiveFamilyProgram.inverse security bits order) =
      reciprocal order (lifted security order (RationalPositiveFamilyProgram.positive security bits order)) := by
  unfold lifted RationalPositiveFamilyProgram.inverse
  rw [_p2mH206, _p2mH201]
open _root_.P2M9e1cfc64 renaming h284 → _p2mH284
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h282 (security order : ℕ) :
    reciprocal order (fun arity =>
      (NormalizedLocalPolynomial.positiveFamily security order (NormalizedLocalPolynomial.independentPositiveLaw security) arity).val) =
      fun arity => (LocalRaisingBounds.positiveInverse security order arity).val := by
  rw [_p2mH204]
  rfl
open _root_.P2M9e1cfc64 renaming h282 → _p2mH282
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h279 (security : ℕ) : 0 ≤ RationalPositiveFamilyProgram.errorConstant security := by
  unfold RationalPositiveFamilyProgram.errorConstant
  exact Finset.sum_nonneg (fun selected _ => _p2mH359 security selected.card)
open _root_.P2M9e1cfc64 renaming h279 → _p2mH279
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h280 (security order : ℕ) : 0 ≤ inverseBound security order := by
  unfold inverseBound
  positivity [_p2mH184 order (1 + PositiveFamilyPointBound.bound security order) 0
    (by positivity [_p2mH140 security order]) (by norm_num)]
open _root_.P2M9e1cfc64 renaming h280 → _p2mH280
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h278 (security order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    |(LocalRaisingBounds.positiveInverse security order arity).val colors centers| ≤ inverseBound security order := by
  have h := _p2mH205 order
    (fun arity => (NormalizedLocalPolynomial.positiveFamily security order
      (NormalizedLocalPolynomial.independentPositiveLaw security) arity).val)
    (PositiveFamilyPointBound.bound security order) (_p2mH140 security order)
    (_p2mH142 security order) arity colors centers
  rw [_p2mH282] at h
  exact h
open _root_.P2M9e1cfc64 renaming h278 → _p2mH278
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h281 (security order : ℕ) : 0 ≤ inverseErrorConstant security order := by
  unfold inverseErrorConstant
  positivity [_p2mH279 security, _p2mH184 order
    (1 + PositiveFamilyPointBound.bound security order) (RationalPositiveFamilyProgram.errorConstant security)
    (by positivity [_p2mH140 security order]) (_p2mH279 security)]
open _root_.P2M9e1cfc64 renaming h281 → _p2mH281
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h283 (security bits order : ℕ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RationalPositiveFamilyProgram.inverse security bits order arity
        (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (LocalRaisingBounds.positiveInverse security order arity).val colors centers| ≤
      inverseErrorConstant security order * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let E := RationalPositiveFamilyProgram.errorConstant security
  let A := PositiveFamilyPointBound.bound security order
  have he : 0 ≤ epsilon := by positivity
  have hE : 0 ≤ E := _p2mH279 security
  have hA : 0 ≤ A := _p2mH140 security order
  have h := _p2mH207 order
    (fun arity => (NormalizedLocalPolynomial.positiveFamily security order
      (NormalizedLocalPolynomial.independentPositiveLaw security) arity).val)
    (lifted security order (RationalPositiveFamilyProgram.positive security bits order)) A (E * epsilon) hA (by positivity)
    (_p2mH142 security order)
    (fun arity colors centers => _p2mH363 security bits order
      hfirst hprecision hbudget arity colors centers) arity colors centers
  rw [← _p2mH284, _p2mH282] at h
  have hsmall : E * epsilon ≤ E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (_p2mH168 bits) hE
  have hg : growth order (1 + A) (E * epsilon) ≤ growth order (1 + A) E := by
    unfold growth
    gcongr
  have hg0 : 0 ≤ growth order (1 + A) (E * epsilon) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (_p2mH184 order (1 + A) (E * epsilon) (by positivity) (by positivity))
  calc
    _ ≤ _ := h
    _ ≤ ((order + 1 : ℕ) : ℝ)^2 * (E * epsilon) * (growth order (1 + A) E)^(order + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0 hg _) (by positivity)
    _ = _ := by unfold inverseErrorConstant; dsimp only [E, A, epsilon]; ring
open _root_.P2M9e1cfc64 renaming h283 → _p2mH283
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h286 (security bits order : ℕ) (compensatorRoot attachmentRoot : ℤ) (primaryColor : ℕ) :
    lifted security order (RationalPositiveFamilyProgram.primaryChannel security bits order compensatorRoot attachmentRoot primaryColor) =
      product order (lifted security order (RationalLocalFamilyProgram.numerator security bits order compensatorRoot attachmentRoot primaryColor))
        (lifted security order (RationalPositiveFamilyProgram.inverse security bits order)) := by
  unfold lifted RationalPositiveFamilyProgram.primaryChannel
  rw [_p2mH197, _p2mH200]
open _root_.P2M9e1cfc64 renaming h286 → _p2mH286
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h285 (security bits order : ℕ) (roots : RootTaggedSelected.RootPair security)
    (primaryColor : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RationalPositiveFamilyProgram.primaryChannel security bits order roots.1.val roots.2.val primaryColor.val arity
        (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.primaryAt security order roots primaryColor arity).val colors centers| ≤
        primaryErrorConstant security order * (1 / (2 : ℝ)^bits) := by
  let numerator := LocalRaisingLinear.completeFamilyLinear security order
    (RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single primaryColor 1)))
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let eN := RationalLocalFamilyProgram.numeratorErrorConstant security
  let eI := inverseErrorConstant security order
  let A := LocalCoefficientPointBounds.numeratorBound security
  let B := inverseBound security order
  have he : 0 ≤ epsilon := by positivity
  have heN : 0 ≤ eN := by
    unfold eN RationalLocalFamilyProgram.numeratorErrorConstant
    exact Finset.sum_nonneg (fun selected _ => _p2mH266 security selected.card)
  have heI : 0 ≤ eI := _p2mH281 security order
  have hA : 0 ≤ A := _p2mH106 security
  have hB : 0 ≤ B := _p2mH280 security order
  have h := _p2mH198 order (fun arity => (numerator arity).val)
    (lifted security order (RationalLocalFamilyProgram.numerator security bits order roots.1.val roots.2.val primaryColor.val))
    (fun arity => (LocalRaisingBounds.positiveInverse security order arity).val)
    (lifted security order (RationalPositiveFamilyProgram.inverse security bits order)) A B (eN * epsilon) (eI * epsilon)
    hA hB (by positivity) (by positivity)
    (_p2mH107 security order roots primaryColor)
    (_p2mH278 security order)
    (fun arity colors centers => _p2mH265 security bits order roots primaryColor
      hfirst hprecision hbudget arity colors centers)
    (fun arity colors centers => _p2mH283 security bits order hfirst hprecision hbudget arity colors centers)
    arity colors centers
  rw [← _p2mH286, _p2mH195] at h
  simp only [Fintype.card_eq_nat_card] at h
  have hsmall : eN * epsilon ≤ eN := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (_p2mH168 bits) heN
  calc
    _ ≤ _ := h
    _ ≤ (Nat.card (TruncatedArity order) : ℝ)^2 *
        ((eN * epsilon) * B + (A + eN) * (eI * epsilon)) := by gcongr
    _ = _ := by unfold primaryErrorConstant; dsimp only [eN, eI, A, B, epsilon]; ring
open _root_.P2M9e1cfc64 renaming h285 → _p2mH285
end
open _root_.P2M9e1cfc64 renaming h278 → _p2mH278
open _root_.P2M9e1cfc64 renaming h279 → _p2mH279
open _root_.P2M9e1cfc64 renaming h280 → _p2mH280
open _root_.P2M9e1cfc64 renaming h281 → _p2mH281
open _root_.P2M9e1cfc64 renaming h282 → _p2mH282
open _root_.P2M9e1cfc64 renaming h283 → _p2mH283
open _root_.P2M9e1cfc64 renaming h284 → _p2mH284
open _root_.P2M9e1cfc64 renaming h285 → _p2mH285
open _root_.P2M9e1cfc64 renaming h286 → _p2mH286
end CurrentAFT.RationalNormalizedPrimaryProgram
open _root_.P2M9e1cfc64 renaming h278 → _p2mH278
open _root_.P2M9e1cfc64 renaming h279 → _p2mH279
open _root_.P2M9e1cfc64 renaming h280 → _p2mH280
open _root_.P2M9e1cfc64 renaming h281 → _p2mH281
open _root_.P2M9e1cfc64 renaming h282 → _p2mH282
open _root_.P2M9e1cfc64 renaming h283 → _p2mH283
open _root_.P2M9e1cfc64 renaming h284 → _p2mH284
open _root_.P2M9e1cfc64 renaming h285 → _p2mH285
open _root_.P2M9e1cfc64 renaming h286 → _p2mH286
end
open _root_.P2M9e1cfc64 renaming h278 → _p2mH278
open _root_.P2M9e1cfc64 renaming h285 → _p2mH285
open _root_.P2M9e1cfc64 renaming h279 → _p2mH279
open _root_.P2M9e1cfc64 renaming h283 → _p2mH283
open _root_.P2M9e1cfc64 renaming h282 → _p2mH282
open _root_.P2M9e1cfc64 renaming h286 → _p2mH286
open _root_.P2M9e1cfc64 renaming h284 → _p2mH284
open _root_.P2M9e1cfc64 renaming h280 → _p2mH280
open _root_.P2M9e1cfc64 renaming h281 → _p2mH281
section
namespace CurrentAFT.RationalSingletonProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls RootTaggedLocal
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram
open UniformBodyProfiles (BodyRole)
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalSingletonProgram.programFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h445 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order)
    (density : Primary → ℝ) (hcenter : ∑ color, primary.weight color * density color = 0) :
    RationalBackgroundTable.firstTable order density (fun _ : Body => 0) =
      fun arity => (BackgroundFamilies.primaryFamily primary body order horder density hcenter arity).val := by
  have hz : ∑ color, body.weight color * (0 : ℝ) = 0 := by simp
  have hk : BackgroundFamilies.bodyKernel primary body (fun _ => 0) hz = 0 := by
    apply Subtype.ext
    rfl
  rw [_p2mH158 primary body order horder density (fun _ => 0) hcenter hz]
  simp only [BackgroundFamilies.bodyFamily, hk, Pi.single_zero, add_zero]
open _root_.P2M9e1cfc64 renaming h445 → _p2mH445
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h451 (security order : ℕ) (horder : 1 ≤ order)
    (profile : Palette security → ℝ) (hzero : ∑ color, profile color = 0) :
    PrimaryMassFamilies.massCertificateFamily security order 1 horder
      (PrimaryMassFamilies.oneWordProfile profile)
      (PrimaryMassFamilies.oneWordProfile_centered profile hzero)
      (PrimaryMassFamilies.oneWordProfile_symmetric profile) =
      BackgroundFamilies.primaryFamily (primaryLaw security) (bodyReference security) order horder
        (RationalMassLiftProgram.actual security profile)
        (by
          change (primaryLaw security).expectation (RationalMassLiftProgram.actual security profile) = 0
          rw [RationalMassLiftProgram.actual, LinearMap.comp_apply,
            PrimaryTensorInverse.densityInverse_mean, profileDensity_mean, hzero, mul_zero]) := by
  unfold PrimaryMassFamilies.massCertificateFamily BackgroundFamilies.primaryFamily
  change Pi.single (M := fun arity : TruncatedArity order =>
      canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val)
    (BackgroundFamilies.primaryArity order horder)
    (PrimaryMassFamilies.massLiftKernel security 1 (PrimaryMassFamilies.oneWordProfile profile)
      (PrimaryMassFamilies.oneWordProfile_centered profile hzero)
      (PrimaryMassFamilies.oneWordProfile_symmetric profile)) = _
  congr 1
  apply Subtype.ext
  funext colors centers
  exact _p2mH277 security profile colors
open _root_.P2M9e1cfc64 renaming h451 → _p2mH451
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h452 (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    RationalBackgroundTable.firstTable order
      (RationalMassLiftProgram.actual security (RootMeanPrimary.meanProfile security role queue))
      (fun _ : SafePalette security => 0) =
      fun arity => (RootMeanPrimary.positiveAtom security order horder role queue arity).val := by
  unfold RootMeanPrimary.positiveAtom
  rw [_p2mH451 security order horder _ (RootMeanPrimary.meanProfile_mass security role queue)]
  exact _p2mH445 _ _ _ _ _ _
open _root_.P2M9e1cfc64 renaming h452 → _p2mH452
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h446 (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (root : CycleRootExpansion.Root security) :
    RationalBackgroundTable.firstTable order (RootReferenceColumns.singletonDensityAt security role queue root)
      (fun _ : SafePalette security => 0) =
      fun arity => (RootReferenceColumns.singletonFirstAt security order horder role queue root arity).val := by
  exact _p2mH445 _ _ _ _ _ _
open _root_.P2M9e1cfc64 renaming h446 → _p2mH446
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h447 (security bits order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (root : CycleRootExpansion.Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(first security bits order role queue root.val arity
      (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.singletonFirstAt security order horder role queue root arity).val colors centers| ≤
      RationalRootProfileProgram.firstErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have h := _p2mH159 order
    (RationalRootProfileProgram.firstDensity security bits role queue root.val) (fun _ => 0)
    (RootReferenceColumns.singletonDensityAt security role queue root) (fun _ : SafePalette security => 0)
    Fin.val (fun color : SafePalette security => color.val.val)
    (RationalRootProfileProgram.firstErrorConstant security * (1 / (2 : ℝ)^bits)) 0
    (by positivity [(_p2mH422 security).1]) (by norm_num)
    (_p2mH425 security bits role queue root hfirst hprecision hbudget)
    (by intro; simp) arity colors centers
  rw [_p2mH446 security order horder role queue root] at h
  simpa only [first, add_zero] using h
open _root_.P2M9e1cfc64 renaming h447 → _p2mH447
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h453 (security bits order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(positive security bits order role queue arity
      (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootMeanPrimary.positiveFamily security order horder role queue arity).val colors centers| ≤
      RationalRootProfileProgram.meanErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have h := _p2mH159 order
    (RationalRootProfileProgram.meanDensity security bits role queue) (fun _ => 0)
    (RationalMassLiftProgram.actual security (RootMeanPrimary.meanProfile security role queue)) (fun _ : SafePalette security => 0)
    Fin.val (fun color : SafePalette security => color.val.val)
    (RationalRootProfileProgram.meanErrorConstant security * (1 / (2 : ℝ)^bits)) 0
    (by positivity [(_p2mH422 security).2]) (by norm_num)
    (_p2mH426 security bits role queue hfirst hprecision hbudget)
    (by intro; simp) arity colors centers
  rw [_p2mH452 security order horder role queue] at h
  have hu := _p2mH364 order security arity colors centers
  have huActual := congrFun (congrFun (congrFun
    (_p2mH208 (primaryLaw security) (bodyReference security) order) arity) colors) centers
  rw [huActual] at hu
  simpa only [positive, Pi.add_apply, Rat.cast_add, hu, RootMeanPrimary.positiveFamily,
    Submodule.coe_add, Pi.add_apply, add_sub_add_left_eq_sub, add_zero] using h
open _root_.P2M9e1cfc64 renaming h453 → _p2mH453
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h444 {Primary Body : Type*} (order : ℕ) (density : Primary → ℝ) (bound : ℝ)
    (hb : 0 ≤ bound) (hdensity : ∀ color, |density color| ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |RationalBackgroundTable.firstTable order density (fun _ => 0) arity colors centers| ≤ bound := by
  unfold RationalBackgroundTable.firstTable
  split_ifs
  · exact hdensity _
  · simpa only [abs_zero] using hb
  · simpa only [abs_zero] using hb
open _root_.P2M9e1cfc64 renaming h444 → _p2mH444
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h454 (security : ℕ) (role : BodyRole) (queue : ℤ) (root : CycleRootExpansion.Root security)
    (output : Palette security) : |deviationProfile security role queue root output| ≤ 2 ∧
      |RootMeanPrimary.meanProfile security role queue output| ≤ 2 := by
  have hatom (law : FiniteDist (Palette security)) : |law.weight output| ≤ 1 := by
    rw [abs_of_nonneg (law.nonneg output)]
    exact law.atom_le_one output
  constructor
  · exact (abs_sub _ _).trans ((add_le_add (hatom _) (hatom _)).trans_eq (by norm_num))
  · exact (abs_sub _ _).trans ((add_le_add (hatom _) (hatom _)).trans_eq (by norm_num))
open _root_.P2M9e1cfc64 renaming h454 → _p2mH454
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h443 (security : ℕ) : 0 ≤ firstBound security := by
  exact mul_nonneg (by norm_num) (_p2mH455 security)
open _root_.P2M9e1cfc64 renaming h443 → _p2mH443
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h438 (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (root : CycleRootExpansion.Root security) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.singletonFirstAt security order horder role queue root arity).val colors centers| ≤ firstBound security := by
  rw [← congrFun (congrFun (congrFun (_p2mH446 security order horder role queue root) arity) colors) centers]
  apply _p2mH444 _ _ _ (_p2mH443 security)
  intro output
  exact (_p2mH268 security (deviationProfile security role queue root) 2 (by norm_num)
    (fun color => (_p2mH454 security role queue root color).1) output).trans_eq (by unfold firstBound; ring)
open _root_.P2M9e1cfc64 renaming h438 → _p2mH438
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h440 (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootMeanPrimary.positiveFamily security order horder role queue arity).val colors centers| ≤ positiveBound security := by
  have hm : |(RootMeanPrimary.positiveAtom security order horder role queue arity).val colors centers| ≤ firstBound security := by
    rw [← congrFun (congrFun (congrFun (_p2mH452 security order horder role queue) arity) colors) centers]
    apply _p2mH444 _ _ _ (_p2mH443 security)
    intro output
    exact (_p2mH268 security (RootMeanPrimary.meanProfile security role queue) 2 (by norm_num)
      (fun color => (_p2mH454 security role queue 0 color).2) output).trans_eq (by unfold firstBound; ring)
  have hu : |((1 : LocalCoefficientFamily.Family security order) arity).val colors centers| ≤ 1 := by
    rw [← congrFun (congrFun (congrFun (_p2mH208 (primaryLaw security) (bodyReference security) order) arity) colors) centers]
    unfold unit
    split_ifs <;> norm_num
  exact (abs_add_le _ _).trans (add_le_add hu hm)
open _root_.P2M9e1cfc64 renaming h440 → _p2mH440
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h450 (security bits order : ℕ) (role : BodyRole) (queue : ℤ) :
    RationalNormalizedPrimaryProgram.lifted security order (inverse security bits order role queue) =
      reciprocal order (RationalNormalizedPrimaryProgram.lifted security order (positive security bits order role queue)) := by
  unfold RationalNormalizedPrimaryProgram.lifted inverse
  rw [_p2mH206, _p2mH201]
open _root_.P2M9e1cfc64 renaming h450 → _p2mH450
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h448 (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    reciprocal order (fun arity => (RootMeanPrimary.positiveFamily security order horder role queue arity).val) =
      fun arity => (RootMeanPrimary.positiveInverse security order horder role queue arity).val := by
  rw [_p2mH204]
  rfl
open _root_.P2M9e1cfc64 renaming h448 → _p2mH448
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h439 (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootMeanPrimary.positiveInverse security order horder role queue arity).val colors centers| ≤ inverseBound security order := by
  have h := _p2mH205 order (fun arity => (RootMeanPrimary.positiveFamily security order horder role queue arity).val)
    (positiveBound security) (by unfold positiveBound; positivity [_p2mH443 security])
    (_p2mH440 security order horder role queue) arity colors centers
  rw [_p2mH448] at h
  exact h
open _root_.P2M9e1cfc64 renaming h439 → _p2mH439
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h449 (security bits order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(inverse security bits order role queue arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootMeanPrimary.positiveInverse security order horder role queue arity).val colors centers| ≤
      inverseErrorConstant security order * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let E := RationalRootProfileProgram.meanErrorConstant security
  let A := positiveBound security
  have he : 0 ≤ epsilon := by positivity
  have hE : 0 ≤ E := (_p2mH422 security).2
  have hA : 0 ≤ A := by unfold A positiveBound; positivity [_p2mH443 security]
  have h := _p2mH207 order
    (fun arity => (RootMeanPrimary.positiveFamily security order horder role queue arity).val)
    (RationalNormalizedPrimaryProgram.lifted security order (positive security bits order role queue)) A (E * epsilon) hA (by positivity)
    (_p2mH440 security order horder role queue)
    (_p2mH453 security bits order horder role queue hfirst hprecision hbudget) arity colors centers
  rw [← _p2mH450, _p2mH448] at h
  have hsmall : E * epsilon ≤ E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (_p2mH168 bits) hE
  have hg : growth order (1 + A) (E * epsilon) ≤ growth order (1 + A) E := by unfold growth; gcongr
  have hg0 : 0 ≤ growth order (1 + A) (E * epsilon) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (_p2mH184 order (1 + A) (E * epsilon) (by positivity) (by positivity))
  calc
    _ ≤ _ := h
    _ ≤ ((order + 1 : ℕ) : ℝ)^2 * (E * epsilon) * (growth order (1 + A) E)^(order + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0 hg _) (by positivity)
    _ = _ := by unfold inverseErrorConstant; dsimp only [E, A, epsilon]; ring
open _root_.P2M9e1cfc64 renaming h449 → _p2mH449
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h442 (security bits order : ℕ) (role : BodyRole) (queue root : ℤ) :
    RationalNormalizedPrimaryProgram.lifted security order (current security bits order role queue root) =
      product order (RationalNormalizedPrimaryProgram.lifted security order (first security bits order role queue root))
        (RationalNormalizedPrimaryProgram.lifted security order (inverse security bits order role queue)) := by
  unfold RationalNormalizedPrimaryProgram.lifted current
  rw [_p2mH197, _p2mH200]
open _root_.P2M9e1cfc64 renaming h442 → _p2mH442
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h441 (security bits order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (root : CycleRootExpansion.Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order role queue root.val arity
      (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.singletonAt security order horder role queue root arity).val colors centers| ≤
      errorConstant security order * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let eN := RationalRootProfileProgram.firstErrorConstant security
  let eI := inverseErrorConstant security order
  let A := firstBound security
  let B := inverseBound security order
  have he : 0 ≤ epsilon := by positivity
  have heN : 0 ≤ eN := (_p2mH422 security).1
  have hA : 0 ≤ A := _p2mH443 security
  have hpos : 0 ≤ positiveBound security := by unfold positiveBound; positivity
  have hg : 1 ≤ growth order (1 + positiveBound security) 0 := _p2mH184 _ _ _ (by positivity) (by norm_num)
  have hB : 0 ≤ B := by unfold B inverseBound; positivity
  have hE := (_p2mH422 security).2
  have hgE := _p2mH184 order (1 + positiveBound security) (RationalRootProfileProgram.meanErrorConstant security)
    (by positivity) hE
  have heI : 0 ≤ eI := by unfold eI inverseErrorConstant; positivity
  have h := _p2mH198 order
    (fun arity => (RootReferenceColumns.singletonFirstAt security order horder role queue root arity).val)
    (RationalNormalizedPrimaryProgram.lifted security order (first security bits order role queue root.val))
    (fun arity => (RootMeanPrimary.positiveInverse security order horder role queue arity).val)
    (RationalNormalizedPrimaryProgram.lifted security order (inverse security bits order role queue)) A B (eN * epsilon) (eI * epsilon)
    hA hB (by positivity) (by positivity) (_p2mH438 security order horder role queue root)
    (_p2mH439 security order horder role queue)
    (_p2mH447 security bits order horder role queue root hfirst hprecision hbudget)
    (_p2mH449 security bits order horder role queue hfirst hprecision hbudget) arity colors centers
  rw [← _p2mH442, _p2mH195] at h
  simp only [Fintype.card_eq_nat_card] at h
  have hsmall : eN * epsilon ≤ eN := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (_p2mH168 bits) heN
  calc
    _ ≤ _ := h
    _ ≤ (Nat.card (TruncatedArity order) : ℝ)^2 *
        ((eN * epsilon) * B + (A + eN) * (eI * epsilon)) := by gcongr
    _ = _ := by unfold errorConstant; dsimp only [eN, eI, A, B, epsilon]; ring
open _root_.P2M9e1cfc64 renaming h441 → _p2mH441
end
open _root_.P2M9e1cfc64 renaming h438 → _p2mH438
open _root_.P2M9e1cfc64 renaming h439 → _p2mH439
open _root_.P2M9e1cfc64 renaming h440 → _p2mH440
open _root_.P2M9e1cfc64 renaming h441 → _p2mH441
open _root_.P2M9e1cfc64 renaming h442 → _p2mH442
open _root_.P2M9e1cfc64 renaming h443 → _p2mH443
open _root_.P2M9e1cfc64 renaming h444 → _p2mH444
open _root_.P2M9e1cfc64 renaming h445 → _p2mH445
open _root_.P2M9e1cfc64 renaming h446 → _p2mH446
open _root_.P2M9e1cfc64 renaming h447 → _p2mH447
open _root_.P2M9e1cfc64 renaming h448 → _p2mH448
open _root_.P2M9e1cfc64 renaming h449 → _p2mH449
open _root_.P2M9e1cfc64 renaming h450 → _p2mH450
open _root_.P2M9e1cfc64 renaming h451 → _p2mH451
open _root_.P2M9e1cfc64 renaming h452 → _p2mH452
open _root_.P2M9e1cfc64 renaming h453 → _p2mH453
open _root_.P2M9e1cfc64 renaming h454 → _p2mH454
end CurrentAFT.RationalSingletonProgram
open _root_.P2M9e1cfc64 renaming h438 → _p2mH438
open _root_.P2M9e1cfc64 renaming h439 → _p2mH439
open _root_.P2M9e1cfc64 renaming h440 → _p2mH440
open _root_.P2M9e1cfc64 renaming h441 → _p2mH441
open _root_.P2M9e1cfc64 renaming h442 → _p2mH442
open _root_.P2M9e1cfc64 renaming h443 → _p2mH443
open _root_.P2M9e1cfc64 renaming h444 → _p2mH444
open _root_.P2M9e1cfc64 renaming h445 → _p2mH445
open _root_.P2M9e1cfc64 renaming h446 → _p2mH446
open _root_.P2M9e1cfc64 renaming h447 → _p2mH447
open _root_.P2M9e1cfc64 renaming h448 → _p2mH448
open _root_.P2M9e1cfc64 renaming h449 → _p2mH449
open _root_.P2M9e1cfc64 renaming h450 → _p2mH450
open _root_.P2M9e1cfc64 renaming h451 → _p2mH451
open _root_.P2M9e1cfc64 renaming h452 → _p2mH452
open _root_.P2M9e1cfc64 renaming h453 → _p2mH453
open _root_.P2M9e1cfc64 renaming h454 → _p2mH454
end
open _root_.P2M9e1cfc64 renaming h451 → _p2mH451
open _root_.P2M9e1cfc64 renaming h441 → _p2mH441
open _root_.P2M9e1cfc64 renaming h449 → _p2mH449
open _root_.P2M9e1cfc64 renaming h438 → _p2mH438
open _root_.P2M9e1cfc64 renaming h452 → _p2mH452
open _root_.P2M9e1cfc64 renaming h448 → _p2mH448
open _root_.P2M9e1cfc64 renaming h444 → _p2mH444
open _root_.P2M9e1cfc64 renaming h442 → _p2mH442
open _root_.P2M9e1cfc64 renaming h445 → _p2mH445
open _root_.P2M9e1cfc64 renaming h443 → _p2mH443
open _root_.P2M9e1cfc64 renaming h440 → _p2mH440
open _root_.P2M9e1cfc64 renaming h447 → _p2mH447
open _root_.P2M9e1cfc64 renaming h439 → _p2mH439
open _root_.P2M9e1cfc64 renaming h450 → _p2mH450
open _root_.P2M9e1cfc64 renaming h446 → _p2mH446
open _root_.P2M9e1cfc64 renaming h454 → _p2mH454
open _root_.P2M9e1cfc64 renaming h453 → _p2mH453
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
theorem _root_.P2M9e1cfc64.h150 (security order : ℕ)
    (first second : RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    interpret security order (RationalFamilyProductProgram.product order first second) =
      RationalFamilyProductProgram.product order (interpret security order first) (interpret security order second) := by
  unfold interpret
  rw [_p2mH197, _p2mH200]
open _root_.P2M9e1cfc64 renaming h150 → _p2mH150
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h149 (security order : ℕ) (first second : ActualFamily security order) :
    RationalFamilyProductProgram.product order (data security order first) (data security order second) =
      data security order (GradedControlAlgebra.familyProduct (ProposalPrimary.primaryLaw security)
        (ActualControls.bodyReference security) order first second) :=
  _p2mH195 _ _ _ _ _
open _root_.P2M9e1cfc64 renaming h149 → _p2mH149
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h151 (security bits order : ℕ)
    (first second : ActualFamily security order)
    (computedFirst computedSecond : RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (A B e f : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hf : 0 ≤ f)
    (ha : ∀ arity colors centers, |data security order first arity colors centers| ≤ A)
    (hb : ∀ arity colors centers, |data security order second arity colors centers| ≤ B)
    (hea : ∀ arity colors centers,
      |interpret security order computedFirst arity colors centers-data security order first arity colors centers| ≤ e*(1/(2:ℝ)^bits))
    (heb : ∀ arity colors centers,
      |interpret security order computedSecond arity colors centers-data security order second arity colors centers| ≤ f*(1/(2:ℝ)^bits))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (RationalFamilyProductProgram.product order computedFirst computedSecond) arity colors centers-
      data security order (GradedControlAlgebra.familyProduct (ProposalPrimary.primaryLaw security)
        (ActualControls.bodyReference security) order first second) arity colors centers| ≤
      productError order A B e f*(1/(2:ℝ)^bits) := by
  have hε : (0:ℝ) ≤ 1/2^bits := by positivity
  have hε1 : 1/(2:ℝ)^bits ≤ 1 :=
    (div_le_one (by positivity : (0:ℝ)<2^bits)).mpr (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  rw [_p2mH150, ← _p2mH149]
  have h := _p2mH198 order
    (data security order first) (interpret security order computedFirst)
    (data security order second) (interpret security order computedSecond)
    A B (e*(1/(2:ℝ)^bits)) (f*(1/(2:ℝ)^bits)) hA hB
    (mul_nonneg he hε) (mul_nonneg hf hε) ha hb hea heb arity colors centers
  apply h.trans
  calc
    _ ≤ (Fintype.card (TruncatedArity order):ℝ)^2*
        ((e*(1/(2:ℝ)^bits))*B+(A+e)*(f*(1/(2:ℝ)^bits))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hAe : A+e*(1/(2:ℝ)^bits) ≤ A+e := by
        nlinarith [mul_le_mul_of_nonneg_left hε1 he]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hAe (mul_nonneg hf hε))
    _ = _ := by unfold productError; ring
open _root_.P2M9e1cfc64 renaming h151 → _p2mH151
end
open _root_.P2M9e1cfc64 renaming h149 → _p2mH149
open _root_.P2M9e1cfc64 renaming h150 → _p2mH150
open _root_.P2M9e1cfc64 renaming h151 → _p2mH151
end CurrentAFT.RationalActualFamilyApproximation
open _root_.P2M9e1cfc64 renaming h149 → _p2mH149
open _root_.P2M9e1cfc64 renaming h150 → _p2mH150
open _root_.P2M9e1cfc64 renaming h151 → _p2mH151
end
open _root_.P2M9e1cfc64 renaming h151 → _p2mH151
open _root_.P2M9e1cfc64 renaming h149 → _p2mH149
open _root_.P2M9e1cfc64 renaming h150 → _p2mH150
section
namespace CurrentAFT.RationalUnselectedLegProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalUnselectedLegProgram.classicalFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h475 (security : ℕ) (root : ℤ) (word : Fin 3 → Palette security) :
    |(ActualBlockFock.primaryLawAt security root).weight word - RootTaggedLegHigher.rawMassLinear security 1 word| ≤ 2 := by
  have hmean : RootTaggedLegHigher.rawMassLinear security 1 word = (RootLegReciprocal.meanPositiveLaw security).weight word :=
    (congrFun (RootLegReciprocal.meanPositiveLaw_weight security) word).symm
  rw [hmean]
  have hfirst : |(ActualBlockFock.primaryLawAt security root).weight word| ≤ 1 := by
    rw [abs_of_nonneg ((ActualBlockFock.primaryLawAt security root).nonneg word)]
    exact (ActualBlockFock.primaryLawAt security root).atom_le_one word
  have hsecond : |(RootLegReciprocal.meanPositiveLaw security).weight word| ≤ 1 := by
    rw [abs_of_nonneg ((RootLegReciprocal.meanPositiveLaw security).nonneg word)]
    exact (RootLegReciprocal.meanPositiveLaw security).atom_le_one word
  exact (abs_sub _ _).trans ((add_le_add hfirst hsecond).trans_eq (by norm_num))
open _root_.P2M9e1cfc64 renaming h475 → _p2mH475
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h470 (security bits order : ℕ) (root : CycleRootExpansion.Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(higher security bits order root.val arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.legHigherAt security order root arity).val colors centers| ≤
      higherError security * (1 / (2 : ℝ)^bits) := by
  exact _p2mH245 security bits order (RationalLegMassProgram.difference security bits root.val)
    ((ActualBlockFock.primaryLawAt security root.val).weight - RootTaggedLegHigher.rawMassLinear security 1)
    2 (RationalLegMassProgram.differenceErrorConstant security) (by norm_num)
    (_p2mH256 security).2 (_p2mH475 security root.val)
    (_p2mH255 security bits root.val hprecision hbudget)
    hfirst hprecision hbudget arity colors centers
open _root_.P2M9e1cfc64 renaming h470 → _p2mH470
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h479 (security bits order : ℕ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(positive security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootLegReciprocal.positive security order arity).val colors centers| ≤
      positiveError security * (1 / (2 : ℝ)^bits) := by
  apply _p2mH250 security bits order (RationalLegMassProgram.mean security bits)
    (RootLegReciprocal.meanPositiveLaw security) (RationalLegMassProgram.meanErrorConstant security)
    (_p2mH256 security).1 _ hfirst hprecision hbudget arity colors centers
  intro word
  rw [RootLegReciprocal.meanPositiveLaw_weight]
  exact _p2mH261 security bits hprecision hbudget word
open _root_.P2M9e1cfc64 renaming h479 → _p2mH479
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h469 (security : ℕ) : 0 ≤ higherError security ∧ 0 ≤ positiveError security := by
  constructor
  · unfold higherError RationalLegFamilyTable.higherError
    exact Finset.sum_nonneg (fun selected _ => _p2mH248 security selected.card 2 _
      (by norm_num) (_p2mH256 security).2)
  · unfold positiveError RationalLegFamilyTable.positiveError
    exact Finset.sum_nonneg (fun selected _ => _p2mH248 security selected.card 1 _
      (by norm_num) (_p2mH256 security).1)
open _root_.P2M9e1cfc64 renaming h469 → _p2mH469
end
open _root_.P2M9e1cfc64 renaming h469 → _p2mH469
open _root_.P2M9e1cfc64 renaming h470 → _p2mH470
open _root_.P2M9e1cfc64 renaming h475 → _p2mH475
open _root_.P2M9e1cfc64 renaming h479 → _p2mH479
end CurrentAFT.RationalUnselectedLegProgram
open _root_.P2M9e1cfc64 renaming h469 → _p2mH469
open _root_.P2M9e1cfc64 renaming h470 → _p2mH470
open _root_.P2M9e1cfc64 renaming h475 → _p2mH475
open _root_.P2M9e1cfc64 renaming h479 → _p2mH479
end
open _root_.P2M9e1cfc64 renaming h470 → _p2mH470
open _root_.P2M9e1cfc64 renaming h469 → _p2mH469
open _root_.P2M9e1cfc64 renaming h479 → _p2mH479
open _root_.P2M9e1cfc64 renaming h475 → _p2mH475
section
namespace CurrentAFT.RationalUnselectedLegProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalUnselectedLegProgram.normalizedFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h478 (security : ℕ) : 0 ≤ positiveBound security := by
  unfold positiveBound
  positivity [_p2mH101 security 1 (by norm_num)]
open _root_.P2M9e1cfc64 renaming h478 → _p2mH478
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h467 (security order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootLegReciprocal.positive security order arity).val colors centers| ≤ positiveBound security :=
  _p2mH100 security order (RootLegReciprocal.meanPositiveLaw security) arity colors centers
open _root_.P2M9e1cfc64 renaming h467 → _p2mH467
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h474 (security bits order : ℕ) :
    interpret security order (inverse security bits order) = reciprocal order (interpret security order (positive security bits order)) := by
  unfold interpret inverse
  rw [_p2mH206, _p2mH201]
open _root_.P2M9e1cfc64 renaming h474 → _p2mH474
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h471 (security order : ℕ) :
    reciprocal order (fun arity => (RootLegReciprocal.positive security order arity).val) =
      fun arity => (RootLegReciprocal.reciprocal security order arity).val := by
  rw [_p2mH204]
  rfl
open _root_.P2M9e1cfc64 renaming h471 → _p2mH471
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h472 (security order : ℕ) : 0 ≤ inverseBound security order ∧ 0 ≤ inverseError security order := by
  have hA := _p2mH478 security
  have hE := (_p2mH469 security).2
  have hg0 := _p2mH184 order (1 + positiveBound security) 0 (by positivity) (by norm_num)
  have hg := _p2mH184 order (1 + positiveBound security) (positiveError security) (by positivity) hE
  constructor
  · unfold inverseBound; positivity
  · unfold inverseError; positivity
open _root_.P2M9e1cfc64 renaming h472 → _p2mH472
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h465 (security order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootLegReciprocal.reciprocal security order arity).val colors centers| ≤ inverseBound security order := by
  have h := _p2mH205 order (fun arity => (RootLegReciprocal.positive security order arity).val)
    (positiveBound security) (_p2mH478 security) (_p2mH467 security order) arity colors centers
  rw [_p2mH471] at h
  exact h
open _root_.P2M9e1cfc64 renaming h465 → _p2mH465
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h473 (security bits order : ℕ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (inverse security bits order) arity colors centers -
      (RootLegReciprocal.reciprocal security order arity).val colors centers| ≤
      inverseError security order * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let E := positiveError security
  let A := positiveBound security
  have he : 0 ≤ epsilon := by positivity
  have hE : 0 ≤ E := (_p2mH469 security).2
  have hA : 0 ≤ A := _p2mH478 security
  have h := _p2mH207 order (fun arity => (RootLegReciprocal.positive security order arity).val)
    (interpret security order (positive security bits order)) A (E * epsilon) hA (by positivity)
    (_p2mH467 security order) (_p2mH479 security bits order hfirst hprecision hbudget) arity colors centers
  rw [← _p2mH474, _p2mH471] at h
  have hsmall : E * epsilon ≤ E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (_p2mH168 bits) hE
  have hg : growth order (1 + A) (E * epsilon) ≤ growth order (1 + A) E := by unfold growth; gcongr
  have hg0 : 0 ≤ growth order (1 + A) (E * epsilon) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (_p2mH184 order (1 + A) (E * epsilon) (by positivity) (by positivity))
  calc
    _ ≤ _ := h
    _ ≤ ((order + 1 : ℕ) : ℝ)^2 * (E * epsilon) * (growth order (1 + A) E)^(order + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0 hg _) (by positivity)
    _ = _ := by unfold inverseError; dsimp only [E, A, epsilon]; ring
open _root_.P2M9e1cfc64 renaming h473 → _p2mH473
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h476 (security : ℕ) : 0 ≤ numeratorBound security ∧ 0 ≤ numeratorError security := by
  exact ⟨add_nonneg (_p2mH443 security)
    (mul_nonneg (by norm_num) (_p2mH101 security 2 (by norm_num))),
    add_nonneg (_p2mH422 security).1 (_p2mH469 security).1⟩
open _root_.P2M9e1cfc64 renaming h476 → _p2mH476
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h466 (security order : ℕ) (horder : 1 ≤ order) (root : CycleRootExpansion.Root security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(numeratorActual security order horder root arity).val colors centers| ≤ numeratorBound security := by
  exact (abs_add_le _ _).trans (add_le_add
    (_p2mH438 security order horder .attachment 0 root arity colors centers)
    (_p2mH97 security order _ 2 (by norm_num) (_p2mH475 security root.val) arity colors centers))
open _root_.P2M9e1cfc64 renaming h466 → _p2mH466
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h477 (security bits order : ℕ) (horder : 1 ≤ order) (root : CycleRootExpansion.Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (numerator security bits order root.val) arity colors centers -
      (numeratorActual security order horder root arity).val colors centers| ≤
      numeratorError security * (1 / (2 : ℝ)^bits) := by
  have hf := _p2mH447 security bits order horder .attachment 0 root hfirst hprecision hbudget arity colors centers
  have hh := _p2mH470 security bits order root hfirst hprecision hbudget arity colors centers
  change |((RationalSingletonProgram.first security bits order .attachment 0 root.val arity _ _ +
    higher security bits order root.val arity _ _ : ℚ) : ℝ) -
    ((RootReferenceColumns.singletonFirstAt security order horder .attachment 0 root arity).val colors centers +
      (RootReferenceColumns.legHigherAt security order root arity).val colors centers)| ≤ _
  rw [Rat.cast_add]
  have hsplit := abs_add_le
    ((RationalSingletonProgram.first security bits order .attachment 0 root.val arity (fun index => (colors index).val)
      (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.singletonFirstAt security order horder .attachment 0 root arity).val colors centers)
    ((higher security bits order root.val arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.legHigherAt security order root arity).val colors centers)
  have hrhs : RationalRootProfileProgram.firstErrorConstant security * (1 / (2 : ℝ)^bits) +
      higherError security * (1 / (2 : ℝ)^bits) = numeratorError security * (1 / (2 : ℝ)^bits) := by
    unfold numeratorError
    ring
  convert hsplit.trans ((add_le_add hf hh).trans_eq hrhs) using 1
  congr 1
  dsimp only [Function.comp_def]
  ring
open _root_.P2M9e1cfc64 renaming h477 → _p2mH477
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h468 (security bits order : ℕ) (horder : 1 ≤ order) (root : CycleRootExpansion.Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order root.val arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.legAt security order horder root arity).val colors centers| ≤
      errorConstant security order * (1 / (2 : ℝ)^bits) := by
  exact _p2mH151 security bits order
    (numeratorActual security order horder root) (RootLegReciprocal.reciprocal security order)
    (numerator security bits order root.val) (inverse security bits order)
    (numeratorBound security) (inverseBound security order) (numeratorError security) (inverseError security order)
    (_p2mH476 security).1 (_p2mH472 security order).1
    (_p2mH476 security).2 (_p2mH472 security order).2
    (_p2mH466 security order horder root) (_p2mH465 security order)
    (_p2mH477 security bits order horder root hfirst hprecision hbudget)
    (_p2mH473 security bits order hfirst hprecision hbudget) arity colors centers
open _root_.P2M9e1cfc64 renaming h468 → _p2mH468
end
open _root_.P2M9e1cfc64 renaming h465 → _p2mH465
open _root_.P2M9e1cfc64 renaming h466 → _p2mH466
open _root_.P2M9e1cfc64 renaming h467 → _p2mH467
open _root_.P2M9e1cfc64 renaming h468 → _p2mH468
open _root_.P2M9e1cfc64 renaming h471 → _p2mH471
open _root_.P2M9e1cfc64 renaming h472 → _p2mH472
open _root_.P2M9e1cfc64 renaming h473 → _p2mH473
open _root_.P2M9e1cfc64 renaming h474 → _p2mH474
open _root_.P2M9e1cfc64 renaming h476 → _p2mH476
open _root_.P2M9e1cfc64 renaming h477 → _p2mH477
open _root_.P2M9e1cfc64 renaming h478 → _p2mH478
end CurrentAFT.RationalUnselectedLegProgram
open _root_.P2M9e1cfc64 renaming h465 → _p2mH465
open _root_.P2M9e1cfc64 renaming h466 → _p2mH466
open _root_.P2M9e1cfc64 renaming h467 → _p2mH467
open _root_.P2M9e1cfc64 renaming h468 → _p2mH468
open _root_.P2M9e1cfc64 renaming h471 → _p2mH471
open _root_.P2M9e1cfc64 renaming h472 → _p2mH472
open _root_.P2M9e1cfc64 renaming h473 → _p2mH473
open _root_.P2M9e1cfc64 renaming h474 → _p2mH474
open _root_.P2M9e1cfc64 renaming h476 → _p2mH476
open _root_.P2M9e1cfc64 renaming h477 → _p2mH477
open _root_.P2M9e1cfc64 renaming h478 → _p2mH478
end
open _root_.P2M9e1cfc64 renaming h465 → _p2mH465
open _root_.P2M9e1cfc64 renaming h471 → _p2mH471
open _root_.P2M9e1cfc64 renaming h478 → _p2mH478
open _root_.P2M9e1cfc64 renaming h466 → _p2mH466
open _root_.P2M9e1cfc64 renaming h474 → _p2mH474
open _root_.P2M9e1cfc64 renaming h476 → _p2mH476
open _root_.P2M9e1cfc64 renaming h472 → _p2mH472
open _root_.P2M9e1cfc64 renaming h473 → _p2mH473
open _root_.P2M9e1cfc64 renaming h477 → _p2mH477
open _root_.P2M9e1cfc64 renaming h468 → _p2mH468
open _root_.P2M9e1cfc64 renaming h467 → _p2mH467
section
namespace CurrentAFT.RationalDiffuseCertificateProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls
  DiffusePair DiffusePairBounds RationalDiffuseResidualProgram
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff Parameters.safeMargin
  PublicParameterProgram.modulus primaryLaw centerLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h180 (security bits : ℕ) (color : Palette security) :
    |(RationalProposalProgram.center security bits color.val : ℝ)| ≤ 1 := by
  change |(RationalProposalProgram.approximateCenterLaw security bits).weight color| ≤ 1
  rw [abs_of_nonneg ((RationalProposalProgram.approximateCenterLaw security bits).nonneg color)]
  exact (RationalProposalProgram.approximateCenterLaw security bits).atom_le_one color
open _root_.P2M9e1cfc64 renaming h180 → _p2mH180
end
open _root_.P2M9e1cfc64 renaming h180 → _p2mH180
end CurrentAFT.RationalDiffuseCertificateProgram
open _root_.P2M9e1cfc64 renaming h180 → _p2mH180
end
open _root_.P2M9e1cfc64 renaming h180 → _p2mH180
section
namespace CurrentAFT.RationalOrdinaryProfileProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalOrdinaryProfileProgram.ordinaryFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalOrdinaryProfileProgram.ordinarySafeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw PublicParameterProgram.modulus
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h307 (security : ℕ) (source center : SafePalette security) :
    centerLinear (bodyReference security) (Pi.single source 1) center =
      (if center.val = source.val then 1 else 0) - (bodyReference security).weight source := by
  simp only [centerLinear, LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.expectation,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have heq : center = source ↔ center.val = source.val := Subtype.ext_iff
  simp only [heq]
open _root_.P2M9e1cfc64 renaming h307 → _p2mH307
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h306 (security : ℕ) (source : SafePalette security) :
    actualPreRoot security source = BodyChannelEvaluation.safeMass security (centerLinear (bodyReference security) (Pi.single source 1)) := by
  have hcenter : (fun center : SafePalette security =>
      (if center.val = source.val then (1 : ℝ) else 0) - (bodyReference security).weight source) =
      centerLinear (bodyReference security) (Pi.single source 1) := by
    funext center
    exact (_p2mH307 security source center).symm
  rw [← hcenter]
  change actualPreRoot security source = BodyChannelEvaluation.safeMass security
    (fun center : SafePalette security =>
      ((if (center.val : Palette security) = source.val then (1 : ℝ) else 0) - (bodyReference security).weight source))
  rw [_p2mH44 security
    (fun color : Palette security => (if color = source.val then 1 else 0) - (bodyReference security).weight source)]
  funext output
  unfold actualPreRoot
  by_cases h : output = source.val
  · subst output
    simp only [if_true]
    rfl
  · simp only [if_neg h]
    ring
open _root_.P2M9e1cfc64 renaming h306 → _p2mH306
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h311 (security : ℕ) (source : SafePalette security) (root : Root security) (output : Palette security) :
    actualPreRoot security source ((shiftEquiv security root.val).symm output) =
      RootMassColumns.ordinaryMassAt security root (centerLinear (bodyReference security) (Pi.single source 1)) output := by
  rw [_p2mH306]
  exact (_p2mH539 security root _ output).symm
open _root_.P2M9e1cfc64 renaming h311 → _p2mH311
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h309 (security bits : ℕ) (source output : Palette security) :
    |(preRoot security bits source.val output.val : ℝ)| ≤ 1 := by
  let hsource := RationalProposalProgram.approximateCenterLaw security bits
  have ha : 0 ≤ (RationalProposalProgram.center security bits source.val : ℝ) := hsource.nonneg source
  have hb : 0 ≤ (RationalProposalProgram.center security bits output.val : ℝ) := hsource.nonneg output
  have hu : (RationalProposalProgram.center security bits output.val : ℝ) ≤ 1 := hsource.atom_le_one output
  rw [preRoot, Rat.cast_mul, Rat.cast_sub, abs_mul]
  have hdelta : |(((if output.val = source.val then 1 else 0) : ℚ) : ℝ) -
      (RationalProposalProgram.center security bits output.val : ℝ)| ≤ 1 := by
    split_ifs <;> norm_num only [Rat.cast_one, Rat.cast_zero] <;> rw [abs_le] <;> constructor <;> linarith
  simpa only [mul_one] using mul_le_mul (_p2mH180 security bits source) hdelta
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
open _root_.P2M9e1cfc64 renaming h309 → _p2mH309
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h310 (security bits : ℕ) (source : SafePalette security) (output : Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(preRoot security bits source.val.val output.val : ℝ) - actualPreRoot security source output| ≤
      profileErrorConstant security * (1 / (2 : ℝ)^bits) := by
  let A := RationalBackgroundDensities.centerErrorConstant security
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  have hA : 0 ≤ A := by unfold A RationalBackgroundDensities.centerErrorConstant; positivity
  have he : 0 ≤ epsilon := by positivity
  have hsource : |(RationalProposalProgram.center security bits source.val.val : ℝ) - (bodyReference security).weight source| ≤ A * epsilon := by
    simpa only [A, epsilon, bodyReference, supportedLaw, centerLaw, RationalBackgroundDensities.centerErrorConstant] using
      _p2mH384 security bits source.val hprecision hbudget
  have houtput : |(RationalProposalProgram.center security bits output.val : ℝ) - (centerLaw security).weight output| ≤ A * epsilon := by
    simpa only [A, epsilon, centerLaw, RationalBackgroundDensities.centerErrorConstant] using
      _p2mH384 security bits output hprecision hbudget
  have hdelta : |((if output.val = source.val.val then 1 else 0 : ℚ) : ℝ) -
      (RationalProposalProgram.center security bits output.val : ℝ)| ≤ 1 := by
    have hb := (RationalProposalProgram.approximateCenterLaw security bits).nonneg output
    have hu := (RationalProposalProgram.approximateCenterLaw security bits).atom_le_one output
    change 0 ≤ (RationalProposalProgram.center security bits output.val : ℝ) at hb
    change (RationalProposalProgram.center security bits output.val : ℝ) ≤ 1 at hu
    split_ifs <;> norm_num only [Rat.cast_one, Rat.cast_zero] <;> rw [abs_le] <;> constructor <;> linarith
  have ha : |(bodyReference security).weight source| ≤ 1 := by
    rw [abs_of_nonneg ((bodyReference security).nonneg source)]
    exact (bodyReference security).atom_le_one source
  rw [preRoot, Rat.cast_mul, Rat.cast_sub]
  have hsame : (((if output.val = source.val.val then (1 : ℚ) else 0) : ℚ) : ℝ) = (if output = source.val then 1 else 0 : ℝ) := by
    by_cases h : output = source.val
    · subst output; simp
    · have hv : output.val ≠ source.val.val := fun heq => h (Fin.ext heq)
      simp [h, hv]
  unfold actualPreRoot
  rw [← hsame]
  have hsplit : (RationalProposalProgram.center security bits source.val.val : ℝ) *
      (((if output.val = source.val.val then 1 else 0 : ℚ) : ℝ) - (RationalProposalProgram.center security bits output.val : ℝ)) -
      (bodyReference security).weight source * (((if output.val = source.val.val then 1 else 0 : ℚ) : ℝ) - (centerLaw security).weight output) =
      ((RationalProposalProgram.center security bits source.val.val : ℝ) - (bodyReference security).weight source) *
        (((if output.val = source.val.val then 1 else 0 : ℚ) : ℝ) - (RationalProposalProgram.center security bits output.val : ℝ)) +
      (bodyReference security).weight source * ((centerLaw security).weight output - (RationalProposalProgram.center security bits output.val : ℝ)) := by ring
  rw [hsplit]
  have hfirst : |((RationalProposalProgram.center security bits source.val.val : ℝ) - (bodyReference security).weight source) *
      (((if output.val = source.val.val then 1 else 0 : ℚ) : ℝ) - (RationalProposalProgram.center security bits output.val : ℝ))| ≤
      (A * epsilon) * 1 := by
    rw [abs_mul]
    exact mul_le_mul hsource hdelta (abs_nonneg _) (by positivity)
  have hsecond : |(bodyReference security).weight source *
      ((centerLaw security).weight output - (RationalProposalProgram.center security bits output.val : ℝ))| ≤ 1 * (A * epsilon) := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul ha houtput (abs_nonneg _) (by norm_num)
  exact (abs_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq
    (by unfold profileErrorConstant; dsimp only [A, epsilon]; ring))
open _root_.P2M9e1cfc64 renaming h310 → _p2mH310
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h308 (security bits : ℕ) (source : SafePalette security) (root : Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(density security bits source.val.val root.val output.val : ℝ) -
      RootReferenceColumns.ordinaryDensityAt security root (Pi.single source 1) output| ≤
      errorConstant security * (1 / (2 : ℝ)^bits) := by
  have hbound (color : Palette security) : |(shifted security bits source.val.val root.val color.val : ℝ)| ≤ 1 := by
    rw [shifted, _p2mH155]
    exact _p2mH309 security bits source.val _
  have hdiff (color : Palette security) : |(shifted security bits source.val.val root.val color.val : ℝ) -
      RootMassColumns.ordinaryMassAt security root (centerLinear (bodyReference security) (Pi.single source 1)) color| ≤
      profileErrorConstant security * (1 / (2 : ℝ)^bits) := by
    rw [shifted, _p2mH155, ← _p2mH311]
    exact _p2mH310 security bits source _ hprecision hbudget
  have h := _p2mH274 security bits (shifted security bits source.val.val root.val) _
    1 (profileErrorConstant security * (1 / (2 : ℝ)^bits)) (by norm_num)
    (by unfold profileErrorConstant RationalBackgroundDensities.centerErrorConstant; positivity)
    hbound hdiff hfirst hprecision hbudget output
  exact h.trans_eq (by unfold errorConstant; ring)
open _root_.P2M9e1cfc64 renaming h308 → _p2mH308
end
open _root_.P2M9e1cfc64 renaming h306 → _p2mH306
open _root_.P2M9e1cfc64 renaming h307 → _p2mH307
open _root_.P2M9e1cfc64 renaming h308 → _p2mH308
open _root_.P2M9e1cfc64 renaming h309 → _p2mH309
open _root_.P2M9e1cfc64 renaming h310 → _p2mH310
open _root_.P2M9e1cfc64 renaming h311 → _p2mH311
end CurrentAFT.RationalOrdinaryProfileProgram
open _root_.P2M9e1cfc64 renaming h306 → _p2mH306
open _root_.P2M9e1cfc64 renaming h307 → _p2mH307
open _root_.P2M9e1cfc64 renaming h308 → _p2mH308
open _root_.P2M9e1cfc64 renaming h309 → _p2mH309
open _root_.P2M9e1cfc64 renaming h310 → _p2mH310
open _root_.P2M9e1cfc64 renaming h311 → _p2mH311
end
open _root_.P2M9e1cfc64 renaming h310 → _p2mH310
open _root_.P2M9e1cfc64 renaming h306 → _p2mH306
open _root_.P2M9e1cfc64 renaming h309 → _p2mH309
open _root_.P2M9e1cfc64 renaming h307 → _p2mH307
open _root_.P2M9e1cfc64 renaming h311 → _p2mH311
open _root_.P2M9e1cfc64 renaming h308 → _p2mH308
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
theorem _root_.P2M9e1cfc64.h548 (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    {r s : ℕ} (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    ((∏ index, primary.weight (sourcePrimary index)) * (∏ index, body.weight (sourceBody index))) •
      (pointKernel primary body hp hb sourcePrimary sourceBody).val =
        symmetrize (weightedTensor primary body sourcePrimary sourceBody) := by
  have hraw : ((∏ index, primary.weight (sourcePrimary index)) * (∏ index, body.weight (sourceBody index))) •
      pointTensor primary body sourcePrimary sourceBody = weightedTensor primary body sourcePrimary sourceBody := by
    funext colors centers
    simp only [Pi.smul_apply, smul_eq_mul, pointTensor, weightedTensor]
    rw [← _p2mH51 primary hp, ← _p2mH51 body hb]
    ring
  have h := congrArg (symmetrizeLinear (Primary := Primary) (Body := Body)) hraw
  rw [map_smul] at h
  exact h
open _root_.P2M9e1cfc64 renaming h548 → _p2mH548
end Generic
open _root_.P2M9e1cfc64 renaming h548 → _p2mH548
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h543 (security : ℕ) {r s : ℕ} (sourcePrimary : Fin r → Palette security)
    (sourceBody : Fin s → SafePalette security) (colors : Fin r → Palette security) (centers : Fin s → SafePalette security) :
    (actualKernel security sourcePrimary sourceBody).val colors centers =
      RationalFamilyProductProgram.average r s (fun primaryOrder bodyOrder =>
        (∏ index, ((if colors (primaryOrder index) = sourcePrimary index then (1 : ℝ) else 0) -
          (primaryLaw security).weight (sourcePrimary index))) *
        ∏ index, ((if centers (bodyOrder index) = sourceBody index then (1 : ℝ) else 0) -
          (bodyReference security).weight (sourceBody index))) := by
  have h := congrFun (congrFun (_p2mH548 (primaryLaw security) (bodyReference security)
    (primaryReference_positive security) (bodyReference_positive security) sourcePrimary sourceBody) colors) centers
  change (actualKernel security sourcePrimary sourceBody).val colors centers = _ at h
  rw [ControlProduct.symmetrize_apply] at h
  simp only [Fintype.card_perm, Fintype.card_fin, weightedTensor, MixedKernel.canonicalPointBasis] at h
  rw [h]
  unfold RationalFamilyProductProgram.average
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
open _root_.P2M9e1cfc64 renaming h543 → _p2mH543
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h542 (security : ℕ) {r s : ℕ} (sourcePrimary : Fin r → Palette security)
    (sourceBody : Fin s → SafePalette security) (colors : Fin r → Palette security) (centers : Fin s → SafePalette security) :
    |(actualKernel security sourcePrimary sourceBody).val colors centers| ≤ 1 := by
  rw [_p2mH543]
  apply _p2mH181
  intro primaryOrder bodyOrder
  rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
  have hproduct {Index Color : Type} [Fintype Index] [Fintype Color] (law : FiniteDist Color)
      (source output : Index → Color) :
      (∏ index, |(if output index = source index then (1 : ℝ) else 0) - law.weight (source index)|) ≤ 1 := by
    apply Finset.prod_le_one
    · intro _ _
      exact abs_nonneg _
    · intro index _
      have hlo := law.nonneg (source index)
      have hhi := law.atom_le_one (source index)
      split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact (mul_le_mul (hproduct (primaryLaw security) sourcePrimary (fun index => colors (primaryOrder index)))
    (hproduct (bodyReference security) sourceBody (fun index => centers (bodyOrder index)))
    (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
open _root_.P2M9e1cfc64 renaming h542 → _p2mH542
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h545 (security bits : ℕ) (source color : SafePalette security) :
    (bodyDelta security bits source.val.val color.val.val : ℝ) =
      (if color = source then (1 : ℝ) else 0) -
        (RationalProposalProgram.approximateBodyReference security bits).weight source := by
  unfold bodyDelta
  by_cases hequal : color = source
  · subst color
    simp only [if_true, Rat.cast_sub, Rat.cast_one]
    rfl
  · have hne : color.val.val ≠ source.val.val := fun h => hequal (Subtype.ext (Fin.ext h))
    simp only [if_neg hne, if_neg hequal, Rat.cast_sub, Rat.cast_zero]
    rfl
open _root_.P2M9e1cfc64 renaming h545 → _p2mH545
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h544 (security bits : ℕ) (source color : SafePalette security) :
    |(bodyDelta security bits source.val.val color.val.val : ℝ)| ≤ 1 := by
  rw [_p2mH545]
  have hlo := (RationalProposalProgram.approximateBodyReference security bits).nonneg source
  have hhi := (RationalProposalProgram.approximateBodyReference security bits).atom_le_one source
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2M9e1cfc64 renaming h544 → _p2mH544
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h546 (security bits : ℕ) (source color : SafePalette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(bodyDelta security bits source.val.val color.val.val : ℝ) -
      ((if color = source then (1 : ℝ) else 0) - (bodyReference security).weight source)| ≤
      (RationalRootMassProgram.primaryErrorConstant security * Parameters.modulus security + 2) * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH545]
  have h := _p2mH382 security bits source hprecision hbudget
  have hequal : ((if color = source then (1 : ℝ) else 0) -
      (RationalProposalProgram.approximateBodyReference security bits).weight source) -
      ((if color = source then (1 : ℝ) else 0) - (bodyReference security).weight source) =
        (bodyReference security).weight source - (RationalProposalProgram.approximateBodyReference security bits).weight source := by ring
  rw [hequal, abs_sub_comm]
  exact h
open _root_.P2M9e1cfc64 renaming h546 → _p2mH546
set_option maxRecDepth 8192
private theorem _root_.P2M9e1cfc64.h562 {Index : Type} [Fintype Index] (value : Index → ℝ)
    (hvalue : ∀ index, |value index| ≤ 1) : |∏ index, value index| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun index _ => hvalue index)
open _root_.P2M9e1cfc64 renaming h562 → _p2mH562
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h547 (security bits r s : ℕ) (sourcePrimary : Fin r → Palette security)
    (sourceBody : Fin s → SafePalette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (colors : Fin r → Palette security) (centers : Fin s → SafePalette security) :
    |(current security bits r s (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)
        (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (actualKernel security sourcePrimary sourceBody).val colors centers| ≤
      errorConstant security r s * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let Cp := RationalRootMassProgram.primaryErrorConstant security
  let Cb : ℝ := Cp * Parameters.modulus security + 2
  have he : 0 ≤ epsilon := by positivity
  have hp : 0 ≤ Cp := by unfold Cp RationalRootMassProgram.primaryErrorConstant; positivity
  have hb : 0 ≤ Cb := by dsimp only [Cb]; positivity
  rw [current, _p2mH182, _p2mH543,
    _p2mH183]
  apply _p2mH181
  intro primaryOrder bodyOrder
  simp only [Rat.cast_mul, Rat.cast_prod]
  let a : Fin r → ℝ := fun index =>
    (RationalPrimaryColumnProgram.centerDelta security bits (sourcePrimary index).val (colors (primaryOrder index)).val : ℝ)
  let b : Fin s → ℝ := fun index =>
    (bodyDelta security bits (sourceBody index).val.val (centers (bodyOrder index)).val.val : ℝ)
  let x : Fin r → ℝ := fun index => (if colors (primaryOrder index) = sourcePrimary index then 1 else 0) -
    (primaryLaw security).weight (sourcePrimary index)
  let y : Fin s → ℝ := fun index => (if centers (bodyOrder index) = sourceBody index then 1 else 0) -
    (bodyReference security).weight (sourceBody index)
  have ha (index : Fin r) : |a index| ≤ 1 := _p2mH374 security bits _ _
  have hb' (index : Fin s) : |b index| ≤ 1 := _p2mH544 security bits _ _
  have hx (index : Fin r) : |x index| ≤ 1 := by
    simpa only [_p2mH372] using
      _p2mH373 security (sourcePrimary index) (colors (primaryOrder index))
  have hy (index : Fin s) : |y index| ≤ 1 := by
    have hlo := (bodyReference security).nonneg (sourceBody index)
    have hhi := (bodyReference security).atom_le_one (sourceBody index)
    dsimp only [y]
    split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  have haprod := _p2mH464 Finset.univ a x 1 (Cp * epsilon)
    (by norm_num) (by positivity) (fun index _ => ha index) (fun index _ => hx index)
    (fun index _ => by
      simpa only [_p2mH372] using
        _p2mH376 security bits (sourcePrimary index) (colors (primaryOrder index)) hprecision hbudget)
  have hbprod := _p2mH464 Finset.univ b y 1 (Cb * epsilon)
    (by norm_num) (by positivity) (fun index _ => hb' index) (fun index _ => hy index)
    (fun index _ => _p2mH546 security bits _ _ hprecision hbudget)
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
      add_le_add (mul_le_mul haprod (_p2mH562 b hb') (abs_nonneg _) (by positivity))
        (mul_le_mul (_p2mH562 x hx) hbprod (abs_nonneg _) (by norm_num))
    _ = _ := by unfold errorConstant; dsimp only [Cp, Cb, epsilon]; ring
open _root_.P2M9e1cfc64 renaming h547 → _p2mH547
end
open _root_.P2M9e1cfc64 renaming h542 → _p2mH542
open _root_.P2M9e1cfc64 renaming h543 → _p2mH543
open _root_.P2M9e1cfc64 renaming h544 → _p2mH544
open _root_.P2M9e1cfc64 renaming h545 → _p2mH545
open _root_.P2M9e1cfc64 renaming h546 → _p2mH546
open _root_.P2M9e1cfc64 renaming h547 → _p2mH547
open _root_.P2M9e1cfc64 renaming h548 → _p2mH548
open _root_.P2M9e1cfc64 renaming h562 → _p2mH562
end CurrentAFT.WeightedPointKernelProgram
open _root_.P2M9e1cfc64 renaming h542 → _p2mH542
open _root_.P2M9e1cfc64 renaming h543 → _p2mH543
open _root_.P2M9e1cfc64 renaming h544 → _p2mH544
open _root_.P2M9e1cfc64 renaming h545 → _p2mH545
open _root_.P2M9e1cfc64 renaming h546 → _p2mH546
open _root_.P2M9e1cfc64 renaming h547 → _p2mH547
open _root_.P2M9e1cfc64 renaming h548 → _p2mH548
open _root_.P2M9e1cfc64 renaming h562 → _p2mH562
end
open _root_.P2M9e1cfc64 renaming h544 → _p2mH544
open _root_.P2M9e1cfc64 renaming h548 → _p2mH548
open _root_.P2M9e1cfc64 renaming h542 → _p2mH542
open _root_.P2M9e1cfc64 renaming h545 → _p2mH545
open _root_.P2M9e1cfc64 renaming h546 → _p2mH546
open _root_.P2M9e1cfc64 renaming h543 → _p2mH543
open _root_.P2M9e1cfc64 renaming h547 → _p2mH547
section
namespace CurrentAFT.RationalOrdinaryFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalOrdinaryFamilyProgram.ordinaryFamilyFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalOrdinaryFamilyProgram.ordinaryFamilySafeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw PublicParameterProgram.modulus
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h298 (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security) :
    RationalBackgroundTable.firstTable order (RootReferenceColumns.ordinaryDensityAt security root (Pi.single source 1))
      (fun _ : SafePalette security => 0) = fun arity => (firstActual security order horder source root arity).val :=
  _p2mH445 _ _ _ _ _ _
open _root_.P2M9e1cfc64 renaming h298 → _p2mH298
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h297 (security : ℕ) : 0 ≤ RationalOrdinaryProfileProgram.errorConstant security := by
  unfold RationalOrdinaryProfileProgram.errorConstant RationalOrdinaryProfileProgram.profileErrorConstant
    RationalBackgroundDensities.centerErrorConstant
  positivity [_p2mH276 security, _p2mH455 security]
open _root_.P2M9e1cfc64 renaming h297 → _p2mH297
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h299 (security bits order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (first security bits order source.val.val root.val) arity colors centers -
      (firstActual security order horder source root arity).val colors centers| ≤
      RationalOrdinaryProfileProgram.errorConstant security * (1 / (2 : ℝ)^bits) := by
  have h := _p2mH159 order
    (RationalOrdinaryProfileProgram.density security bits source.val.val root.val) (fun _ => 0)
    (RootReferenceColumns.ordinaryDensityAt security root (Pi.single source 1)) (fun _ : SafePalette security => 0)
    Fin.val (fun color : SafePalette security => color.val.val)
    (RationalOrdinaryProfileProgram.errorConstant security * (1 / (2 : ℝ)^bits)) 0
    (by positivity [_p2mH297 security]) (by norm_num)
    (_p2mH308 security bits source root hfirst hprecision hbudget)
    (by intro; simp) arity colors centers
  rw [_p2mH298 security order horder source root] at h
  simpa only [interpret, realTable, pullback, first, Function.comp_def, add_zero] using h
open _root_.P2M9e1cfc64 renaming h299 → _p2mH299
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h293 (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) :
    RationalBackgroundTable.firstTable order (fun _ : Palette security => 0)
      (centerLinear (bodyReference security) (Pi.single source 1)) =
      fun arity => (RaisingChannels.bodyLeading security order horder (Pi.single source 1) arity).val := by
  have hz : ∑ color, (primaryLaw security).weight color * (0 : ℝ) = 0 := by simp
  have hk : BackgroundFamilies.primaryKernel (primaryLaw security) (bodyReference security) (fun _ => 0) hz = 0 := by
    apply Subtype.ext; rfl
  rw [_p2mH158 _ _ _ _ _ _ hz (center_mean _ _)]
  simp only [BackgroundFamilies.primaryFamily, hk, Pi.single_zero, zero_add]
  rfl
open _root_.P2M9e1cfc64 renaming h293 → _p2mH293
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h294 (security bits order : ℕ) (horder : 1 ≤ order) (source : SafePalette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (bodyFirst security bits order source.val.val) arity colors centers -
      (RaisingChannels.bodyLeading security order horder (Pi.single source 1) arity).val colors centers| ≤
      RationalBackgroundDensities.centerErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have hcenter (color : SafePalette security) : centerLinear (bodyReference security) (Pi.single source 1) color =
      (if color = source then 1 else 0) - (bodyReference security).weight source := by
    simp [centerLinear, FiniteDist.expectation, Pi.single_apply, mul_ite]
  have hd (color : SafePalette security) :
      |(WeightedPointKernelProgram.bodyDelta security bits source.val.val color.val.val : ℝ) -
        centerLinear (bodyReference security) (Pi.single source 1) color| ≤
        RationalBackgroundDensities.centerErrorConstant security * (1 / (2 : ℝ)^bits) := by
    rw [hcenter]
    exact _p2mH546 security bits source color hprecision hbudget
  have h := _p2mH159 order (fun _ => 0)
    (WeightedPointKernelProgram.bodyDelta security bits source.val.val) (fun _ : Palette security => 0)
    (centerLinear (bodyReference security) (Pi.single source 1)) Fin.val (fun color : SafePalette security => color.val.val)
    0 (RationalBackgroundDensities.centerErrorConstant security * (1 / (2 : ℝ)^bits)) (by norm_num)
    (by unfold RationalBackgroundDensities.centerErrorConstant; positivity) (by intro; simp) hd arity colors centers
  rw [_p2mH293 security order horder source] at h
  simpa only [interpret, realTable, pullback, bodyFirst, Function.comp_def, zero_add] using h
open _root_.P2M9e1cfc64 renaming h294 → _p2mH294
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h295 {Color : Type*} [Fintype Color] (law : FiniteDist Color) (source color : Color) :
    |centerLinear law (Pi.single source 1) color| ≤ 1 := by
  have hlo := law.nonneg source
  have hhi := law.atom_le_one source
  simp only [centerLinear, LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.expectation, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2M9e1cfc64 renaming h295 → _p2mH295
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h305 {Source Output : Type*} [Fintype Source] [Fintype Output]
    (law : FiniteDist Source) (embedding : Source → Output) (score : Source → ℝ)
    (hscore : ∀ source, |score source| ≤ 1) (output : Output) :
    |SelectedOrdinaryRoot.pushLinear law embedding score output| ≤ 1 := by
  change |∑ source, if embedding source = output then law.weight source * score source else 0| ≤ 1
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ source, law.weight source := by
      apply Finset.sum_le_sum
      intro source _
      split_ifs
      · rw [abs_mul, abs_of_nonneg (law.nonneg source)]
        exact (mul_le_mul_of_nonneg_left (hscore source) (law.nonneg source)).trans_eq (mul_one _)
      · simpa only [abs_zero] using law.nonneg source
    _ = 1 := law.sum_one
open _root_.P2M9e1cfc64 renaming h305 → _p2mH305
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h289 (security : ℕ) (source : SafePalette security) (root : Root security) (output : Palette security) :
    |RootReferenceColumns.ordinaryDensityAt security root (Pi.single source 1) output| ≤ RationalTensorInverseProgram.actualBound security := by
  have hprofile (color : Palette security) :
      |RootMassColumns.ordinaryMassAt security root (centerLinear (bodyReference security) (Pi.single source 1)) color| ≤ 1 :=
    _p2mH305 (bodyReference security) _ _ (_p2mH295 (bodyReference security) source) color
  have h := _p2mH268 security _ 1 (by norm_num) hprofile output
  simpa only [RootReferenceColumns.ordinaryDensityAt, RationalMassLiftProgram.actual, LinearMap.comp_apply, mul_one] using h
open _root_.P2M9e1cfc64 renaming h289 → _p2mH289
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h290 (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(firstActual security order horder source root arity).val colors centers| ≤ RationalTensorInverseProgram.actualBound security := by
  rw [← congrFun (congrFun (congrFun (_p2mH298 security order horder source root) arity) colors) centers]
  exact _p2mH444 _ _ _ (_p2mH455 security)
    (_p2mH289 security source root) arity colors centers
open _root_.P2M9e1cfc64 renaming h290 → _p2mH290
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h288 (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RaisingChannels.bodyLeading security order horder (Pi.single source 1) arity).val colors centers| ≤ 1 := by
  rw [← congrFun (congrFun (congrFun (_p2mH293 security order horder source) arity) colors) centers]
  unfold RationalBackgroundTable.firstTable
  split_ifs
  · norm_num
  · exact _p2mH295 (bodyReference security) source _
  · norm_num
open _root_.P2M9e1cfc64 renaming h288 → _p2mH288
end
open _root_.P2M9e1cfc64 renaming h288 → _p2mH288
open _root_.P2M9e1cfc64 renaming h289 → _p2mH289
open _root_.P2M9e1cfc64 renaming h290 → _p2mH290
open _root_.P2M9e1cfc64 renaming h293 → _p2mH293
open _root_.P2M9e1cfc64 renaming h294 → _p2mH294
open _root_.P2M9e1cfc64 renaming h295 → _p2mH295
open _root_.P2M9e1cfc64 renaming h297 → _p2mH297
open _root_.P2M9e1cfc64 renaming h298 → _p2mH298
open _root_.P2M9e1cfc64 renaming h299 → _p2mH299
open _root_.P2M9e1cfc64 renaming h305 → _p2mH305
end CurrentAFT.RationalOrdinaryFamilyProgram
open _root_.P2M9e1cfc64 renaming h288 → _p2mH288
open _root_.P2M9e1cfc64 renaming h289 → _p2mH289
open _root_.P2M9e1cfc64 renaming h290 → _p2mH290
open _root_.P2M9e1cfc64 renaming h293 → _p2mH293
open _root_.P2M9e1cfc64 renaming h294 → _p2mH294
open _root_.P2M9e1cfc64 renaming h295 → _p2mH295
open _root_.P2M9e1cfc64 renaming h297 → _p2mH297
open _root_.P2M9e1cfc64 renaming h298 → _p2mH298
open _root_.P2M9e1cfc64 renaming h299 → _p2mH299
open _root_.P2M9e1cfc64 renaming h305 → _p2mH305
end
open _root_.P2M9e1cfc64 renaming h295 → _p2mH295
open _root_.P2M9e1cfc64 renaming h298 → _p2mH298
open _root_.P2M9e1cfc64 renaming h289 → _p2mH289
open _root_.P2M9e1cfc64 renaming h293 → _p2mH293
open _root_.P2M9e1cfc64 renaming h290 → _p2mH290
open _root_.P2M9e1cfc64 renaming h299 → _p2mH299
open _root_.P2M9e1cfc64 renaming h297 → _p2mH297
open _root_.P2M9e1cfc64 renaming h288 → _p2mH288
open _root_.P2M9e1cfc64 renaming h305 → _p2mH305
open _root_.P2M9e1cfc64 renaming h294 → _p2mH294
section
namespace CurrentAFT.RootOrdinaryDataIdentity
open AFT
open scoped Classical
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h495 (security : ℕ) :
    RootMeanPrimary.meanProfile security .free 0 = OrdinaryRaising.deviation security := by
  unfold RootMeanPrimary.meanProfile OrdinaryRaising.deviation
  rw [_p2mH485, RootLocalDenominators.uniformReference_eq]
open _root_.P2M9e1cfc64 renaming h495 → _p2mH495
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h496 (security order : ℕ) (horder : 1 ≤ order) :
    RootMeanPrimary.positiveAtom security order horder .free 0 = OrdinaryRaising.positiveAtom security order horder := by
  unfold RootMeanPrimary.positiveAtom OrdinaryRaising.positiveAtom
  congr 1
  exact congrArg PrimaryMassFamilies.oneWordProfile (_p2mH495 security)
open _root_.P2M9e1cfc64 renaming h496 → _p2mH496
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h497 (security order : ℕ) (horder : 1 ≤ order) :
    RootMeanPrimary.positiveFamily security order horder .free 0 = OrdinaryRaising.positiveFamily security order horder := by
  unfold RootMeanPrimary.positiveFamily OrdinaryRaising.positiveFamily
  rw [_p2mH496]
open _root_.P2M9e1cfc64 renaming h497 → _p2mH497
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h498 (security order : ℕ) (horder : 1 ≤ order) :
    RootMeanPrimary.positiveInverse security order horder .free 0 = OrdinaryRaising.positiveInverse security order horder := by
  unfold RootMeanPrimary.positiveInverse OrdinaryRaising.positiveInverse
  rw [_p2mH497]
open _root_.P2M9e1cfc64 renaming h498 → _p2mH498
end
open _root_.P2M9e1cfc64 renaming h495 → _p2mH495
open _root_.P2M9e1cfc64 renaming h496 → _p2mH496
open _root_.P2M9e1cfc64 renaming h497 → _p2mH497
open _root_.P2M9e1cfc64 renaming h498 → _p2mH498
end CurrentAFT.RootOrdinaryDataIdentity
open _root_.P2M9e1cfc64 renaming h495 → _p2mH495
open _root_.P2M9e1cfc64 renaming h496 → _p2mH496
open _root_.P2M9e1cfc64 renaming h497 → _p2mH497
open _root_.P2M9e1cfc64 renaming h498 → _p2mH498
end
open _root_.P2M9e1cfc64 renaming h496 → _p2mH496
open _root_.P2M9e1cfc64 renaming h498 → _p2mH498
open _root_.P2M9e1cfc64 renaming h495 → _p2mH495
open _root_.P2M9e1cfc64 renaming h497 → _p2mH497
namespace CurrentAFT.RootOrdinaryDataIdentity
end CurrentAFT.RootOrdinaryDataIdentity
section
namespace CurrentAFT.RationalOrdinaryFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalOrdinaryFamilyProgram.ordinaryNormalizedFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalOrdinaryFamilyProgram.ordinaryNormalizedSafeDecidableEq
attribute [local irreducible] Parameters.base primaryLaw centerLaw rootReference PublicParameterProgram.modulus
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h301 (security order : ℕ) : 0 ≤ RationalSingletonProgram.inverseBound security order ∧
    0 ≤ RationalSingletonProgram.inverseErrorConstant security order := by
  have hfirst := _p2mH443 security
  have hpos : 0 ≤ RationalSingletonProgram.positiveBound security := by unfold RationalSingletonProgram.positiveBound; positivity
  have hE := (_p2mH422 security).2
  have hg0 := _p2mH184 order (1 + RationalSingletonProgram.positiveBound security) 0 (by positivity) (by norm_num)
  have hg := _p2mH184 order (1 + RationalSingletonProgram.positiveBound security)
    (RationalRootProfileProgram.meanErrorConstant security) (by positivity) hE
  constructor
  · unfold RationalSingletonProgram.inverseBound; positivity
  · unfold RationalSingletonProgram.inverseErrorConstant; positivity
open _root_.P2M9e1cfc64 renaming h301 → _p2mH301
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h302 (security bits order : ℕ) (horder : 1 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (RationalSingletonProgram.inverse security bits order .free 0) arity colors centers -
      (OrdinaryRaising.positiveInverse security order horder arity).val colors centers| ≤
      RationalSingletonProgram.inverseErrorConstant security order * (1 / (2 : ℝ)^bits) := by
  have h := _p2mH449 security bits order horder .free 0 hfirst hprecision hbudget arity colors centers
  rw [_p2mH498] at h
  exact h
open _root_.P2M9e1cfc64 renaming h302 → _p2mH302
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h291 (security order : ℕ) (horder : 1 ≤ order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(OrdinaryRaising.positiveInverse security order horder arity).val colors centers| ≤
      RationalSingletonProgram.inverseBound security order := by
  have h := _p2mH439 security order horder .free 0 arity colors centers
  rw [_p2mH498] at h
  exact h
open _root_.P2M9e1cfc64 renaming h291 → _p2mH291
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h292 (security bits order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (atRoot security bits order source.val.val root.val) arity colors centers -
      (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers| ≤
      atRootError security order * (1 / (2 : ℝ)^bits) := by
  exact _p2mH151 security bits order
    (firstActual security order horder source root) (OrdinaryRaising.positiveInverse security order horder)
    (first security bits order source.val.val root.val) (RationalSingletonProgram.inverse security bits order .free 0)
    (RationalTensorInverseProgram.actualBound security) (RationalSingletonProgram.inverseBound security order)
    (RationalOrdinaryProfileProgram.errorConstant security) (RationalSingletonProgram.inverseErrorConstant security order)
    (_p2mH455 security) (_p2mH301 security order).1
    (_p2mH297 security) (_p2mH301 security order).2
    (_p2mH290 security order horder source root) (_p2mH291 security order horder)
    (_p2mH299 security bits order horder source root hfirst hprecision hbudget)
    (_p2mH302 security bits order horder hfirst hprecision hbudget) arity colors centers
open _root_.P2M9e1cfc64 renaming h292 → _p2mH292
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h300 (security bits order : ℕ) (horder : 1 ≤ order) (source : SafePalette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (independent security bits order source.val.val) arity colors centers -
      (SelectedOrdinaryHybrid.independentChannel security order horder (Pi.single source 1) arity).val colors centers| ≤
      independentError security order * (1 / (2 : ℝ)^bits) := by
  exact _p2mH151 security bits order
    (RaisingChannels.bodyLeading security order horder (Pi.single source 1)) (OrdinaryRaising.positiveInverse security order horder)
    (bodyFirst security bits order source.val.val) (RationalSingletonProgram.inverse security bits order .free 0)
    1 (RationalSingletonProgram.inverseBound security order) (RationalBackgroundDensities.centerErrorConstant security)
    (RationalSingletonProgram.inverseErrorConstant security order) (by norm_num) (_p2mH301 security order).1
    (by unfold RationalBackgroundDensities.centerErrorConstant; positivity) (_p2mH301 security order).2
    (_p2mH288 security order horder source) (_p2mH291 security order horder)
    (_p2mH294 security bits order horder source hprecision hbudget)
    (_p2mH302 security bits order horder hfirst hprecision hbudget) arity colors centers
open _root_.P2M9e1cfc64 renaming h300 → _p2mH300
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h287 (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers| ≤
      atRootBound security order := by
  have h := _p2mH196 order (data security order (firstActual security order horder source root))
    (data security order (OrdinaryRaising.positiveInverse security order horder))
    (RationalTensorInverseProgram.actualBound security) (RationalSingletonProgram.inverseBound security order)
    (_p2mH455 security) (_p2mH301 security order).1
    (_p2mH290 security order horder source root) (_p2mH291 security order horder) arity colors centers
  rw [_p2mH149] at h
  exact h
open _root_.P2M9e1cfc64 renaming h287 → _p2mH287
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h304 (security bits order source : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    interpret security order (mean security bits order source) arity colors centers =
      ∑ root : Root security, (RootSignedMassProgram.referenceEntry security bits root.val : ℝ) *
        interpret security order (atRoot security bits order source root.val) arity colors centers := by
  change ((∑ root : Fin (PublicParameterProgram.modulus security).count,
    RootSignedMassProgram.referenceEntry security bits root.val *
      atRoot security bits order source root.val arity (fun index => (colors index).val)
        (fun index => (centers index).val.val) : ℚ) : ℝ) = _
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul]
  calc
    _ = ∑ root : Palette security, (RootSignedMassProgram.referenceEntry security bits ((ZMod.finEquiv (Parameters.modulus security)) root).val : ℝ) *
        interpret security order (atRoot security bits order source ((ZMod.finEquiv (Parameters.modulus security)) root).val) arity colors centers := by
      apply Finset.sum_congr (by ext; simp)
      intro root _
      simp only [_p2mH257]
      rfl
    _ = _ := (ZMod.finEquiv (Parameters.modulus security)).toEquiv.sum_comp (fun root : Root security =>
      (RootSignedMassProgram.referenceEntry security bits root.val : ℝ) *
        interpret security order (atRoot security bits order source root.val) arity colors centers)
open _root_.P2M9e1cfc64 renaming h304 → _p2mH304
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h303 (security bits order : ℕ) (horder : 1 ≤ order) (source : SafePalette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (mean security bits order source.val.val) arity colors centers -
      ∑ root : Root security, (rootReference security).weight root *
        (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers| ≤
      meanError security order * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH304, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _root : Root security, (atRootError security order + 2 * atRootBound security order) * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro root _
      have hr := _p2mH520 security bits root
      have he := _p2mH522 security bits root
      have ha := _p2mH292 security bits order horder source root hfirst hprecision hbudget arity colors centers
      have hb := _p2mH287 security order horder source root arity colors centers
      calc
        _ = |(RootSignedMassProgram.referenceEntry security bits root.val : ℝ) *
            (interpret security order (atRoot security bits order source.val.val root.val) arity colors centers -
              (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers) +
            ((RootSignedMassProgram.referenceEntry security bits root.val : ℝ) - (rootReference security).weight root) *
              (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ 1 * (atRootError security order * (1 / (2 : ℝ)^bits)) + (2 / (2 : ℝ)^bits) * atRootBound security order := by
          simp only [abs_mul]
          exact add_le_add (mul_le_mul (by rw [abs_of_nonneg hr.1]; exact hr.2) ha (abs_nonneg _) (by norm_num))
            (mul_le_mul he hb (abs_nonneg _) (by positivity))
        _ = _ := by ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; unfold meanError; ring
open _root_.P2M9e1cfc64 renaming h303 → _p2mH303
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h296 (security bits order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (current security bits order source.val.val root.val) arity colors centers -
      (RootReferenceColumns.hybridAt security order horder root (Pi.single source 1) arity).val colors centers| ≤
      errorConstant security order * (1 / (2 : ℝ)^bits) := by
  have hi := _p2mH300 security bits order horder source hfirst hprecision hbudget arity colors centers
  have ha := _p2mH292 security bits order horder source root hfirst hprecision hbudget arity colors centers
  have hm := _p2mH303 security bits order horder source hfirst hprecision hbudget arity colors centers
  have htarget : (RootReferenceColumns.hybridAt security order horder root (Pi.single source 1) arity).val colors centers =
      (SelectedOrdinaryHybrid.independentChannel security order horder (Pi.single source 1) arity).val colors centers +
        (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers -
      ∑ other : Root security, (rootReference security).weight other *
        (RootReferenceColumns.ordinaryAt security order horder other (Pi.single source 1) arity).val colors centers := by
    simp only [RootReferenceColumns.hybridAt, Pi.sub_apply, Pi.add_apply, Submodule.coe_sub, Submodule.coe_add,
      Finset.sum_apply, Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hcurrent : interpret security order (current security bits order source.val.val root.val) arity colors centers =
      interpret security order (independent security bits order source.val.val) arity colors centers +
        interpret security order (atRoot security bits order source.val.val root.val) arity colors centers -
      interpret security order (mean security bits order source.val.val) arity colors centers := by
    simp only [interpret, realTable, pullback, current, Pi.sub_apply, Pi.add_apply, Rat.cast_sub, Rat.cast_add]
  rw [hcurrent, htarget]
  have hsplit : interpret security order (independent security bits order source.val.val) arity colors centers +
      interpret security order (atRoot security bits order source.val.val root.val) arity colors centers -
      interpret security order (mean security bits order source.val.val) arity colors centers -
      ((SelectedOrdinaryHybrid.independentChannel security order horder (Pi.single source 1) arity).val colors centers +
        (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers -
        ∑ other : Root security, (rootReference security).weight other *
          (RootReferenceColumns.ordinaryAt security order horder other (Pi.single source 1) arity).val colors centers) =
      (interpret security order (independent security bits order source.val.val) arity colors centers -
        (SelectedOrdinaryHybrid.independentChannel security order horder (Pi.single source 1) arity).val colors centers) +
      (interpret security order (atRoot security bits order source.val.val root.val) arity colors centers -
        (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers) -
      (interpret security order (mean security bits order source.val.val) arity colors centers -
        ∑ other : Root security, (rootReference security).weight other *
          (RootReferenceColumns.ordinaryAt security order horder other (Pi.single source 1) arity).val colors centers) := by ring
  rw [hsplit]
  exact (abs_sub _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add hi ha)) hm).trans_eq (by unfold errorConstant; ring))
open _root_.P2M9e1cfc64 renaming h296 → _p2mH296
end
open _root_.P2M9e1cfc64 renaming h287 → _p2mH287
open _root_.P2M9e1cfc64 renaming h291 → _p2mH291
open _root_.P2M9e1cfc64 renaming h292 → _p2mH292
open _root_.P2M9e1cfc64 renaming h296 → _p2mH296
open _root_.P2M9e1cfc64 renaming h300 → _p2mH300
open _root_.P2M9e1cfc64 renaming h301 → _p2mH301
open _root_.P2M9e1cfc64 renaming h302 → _p2mH302
open _root_.P2M9e1cfc64 renaming h303 → _p2mH303
open _root_.P2M9e1cfc64 renaming h304 → _p2mH304
end CurrentAFT.RationalOrdinaryFamilyProgram
open _root_.P2M9e1cfc64 renaming h287 → _p2mH287
open _root_.P2M9e1cfc64 renaming h291 → _p2mH291
open _root_.P2M9e1cfc64 renaming h292 → _p2mH292
open _root_.P2M9e1cfc64 renaming h296 → _p2mH296
open _root_.P2M9e1cfc64 renaming h300 → _p2mH300
open _root_.P2M9e1cfc64 renaming h301 → _p2mH301
open _root_.P2M9e1cfc64 renaming h302 → _p2mH302
open _root_.P2M9e1cfc64 renaming h303 → _p2mH303
open _root_.P2M9e1cfc64 renaming h304 → _p2mH304
end
open _root_.P2M9e1cfc64 renaming h304 → _p2mH304
open _root_.P2M9e1cfc64 renaming h303 → _p2mH303
open _root_.P2M9e1cfc64 renaming h302 → _p2mH302
open _root_.P2M9e1cfc64 renaming h292 → _p2mH292
open _root_.P2M9e1cfc64 renaming h296 → _p2mH296
open _root_.P2M9e1cfc64 renaming h287 → _p2mH287
open _root_.P2M9e1cfc64 renaming h291 → _p2mH291
open _root_.P2M9e1cfc64 renaming h301 → _p2mH301
open _root_.P2M9e1cfc64 renaming h300 → _p2mH300
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
theorem _root_.P2M9e1cfc64.h394 (security order : ℕ) : 0 ≤ errorConstant security order := by unfold errorConstant; positivity
open _root_.P2M9e1cfc64 renaming h394 → _p2mH394
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h398 {security r s : ℕ} (bits order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : TaggedSelection.Selection security r s) (tagged : Finset (ActualBlockFock.BlockIndex security))
    (group : PairedRootPlacement.ActiveGroup selection tagged) (source : ActualRootGroupedChannel.Input selection tagged group)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (table bits order queue selection tagged group source) arity colors centers -
      (RootReferenceColumns.reducedColumn order horder queue selection tagged group source arity).val colors centers| ≤
      errorConstant security order * (1 / (2 : ℝ)^bits) := by
  have he : 0 ≤ 1 / (2 : ℝ)^bits := by positivity
  have hp : RationalNormalizedPrimaryProgram.primaryErrorConstant security order ≤ errorConstant security order := by
    unfold errorConstant
    linarith [le_abs_self (RationalNormalizedPrimaryProgram.primaryErrorConstant security order),
      abs_nonneg (RationalOrdinaryFamilyProgram.errorConstant security order),
      abs_nonneg (RationalUnselectedLegProgram.errorConstant security order), abs_nonneg (RationalSingletonProgram.errorConstant security order)]
  have ho : RationalOrdinaryFamilyProgram.errorConstant security order ≤ errorConstant security order := by
    unfold errorConstant
    linarith [le_abs_self (RationalOrdinaryFamilyProgram.errorConstant security order),
      abs_nonneg (RationalNormalizedPrimaryProgram.primaryErrorConstant security order),
      abs_nonneg (RationalUnselectedLegProgram.errorConstant security order), abs_nonneg (RationalSingletonProgram.errorConstant security order)]
  have hl : RationalUnselectedLegProgram.errorConstant security order ≤ errorConstant security order := by
    unfold errorConstant
    linarith [le_abs_self (RationalUnselectedLegProgram.errorConstant security order),
      abs_nonneg (RationalNormalizedPrimaryProgram.primaryErrorConstant security order),
      abs_nonneg (RationalOrdinaryFamilyProgram.errorConstant security order), abs_nonneg (RationalSingletonProgram.errorConstant security order)]
  have hs : RationalSingletonProgram.errorConstant security order ≤ errorConstant security order := by
    unfold errorConstant
    linarith [le_abs_self (RationalSingletonProgram.errorConstant security order),
      abs_nonneg (RationalNormalizedPrimaryProgram.primaryErrorConstant security order),
      abs_nonneg (RationalUnselectedLegProgram.errorConstant security order), abs_nonneg (RationalOrdinaryFamilyProgram.errorConstant security order)]
  rcases group with (primary | ordinary) | kept
  · have h := _p2mH285 security bits order
      (RootPrimaryGroupedChannel.pairEquiv security source.1) source.2 hfirst hprecision hbudget arity colors centers
    exact h.trans (mul_le_mul_of_nonneg_right hp he)
  · exact (_p2mH296 security bits order horder source.2 (source.1 (0 : Fin 1))
      hfirst hprecision hbudget arity colors centers).trans (mul_le_mul_of_nonneg_right ho he)
  · rcases hk : kept.val.val with leg | (center | point)
    · simpa only [table, role, hk, sourceNatural, localTable, Matrix.cons_val_zero,
        RootReferenceColumns.reducedColumn, RootReferenceColumns.unselectedAt, interpret, realTable, pullback, Function.comp_def] using
        (_p2mH468 security bits order horder (source.1 (0 : Fin 1))
          hfirst hprecision hbudget arity colors centers).trans (mul_le_mul_of_nonneg_right hl he)
    · have hfree : RootReferenceColumns.singletonAt security order horder .free queue (source.1 (0 : Fin 1)) =
          RootReferenceColumns.singletonAt security order horder .free 0 (source.1 (0 : Fin 1)) := by rfl
      simpa only [table, role, hk, sourceNatural, localTable, Matrix.cons_val_zero,
        RootReferenceColumns.reducedColumn, RootReferenceColumns.unselectedAt, interpret, realTable, pullback, Function.comp_def, hfree] using
        (_p2mH441 security bits order horder .free queue (source.1 (0 : Fin 1))
          hfirst hprecision hbudget arity colors centers).trans (mul_le_mul_of_nonneg_right hs he)
    · simpa only [table, role, hk, sourceNatural, localTable, Matrix.cons_val_zero,
        RootReferenceColumns.reducedColumn, RootReferenceColumns.unselectedAt, interpret, realTable, pullback, Function.comp_def] using
        (_p2mH441 security bits order horder .queue queue (source.1 (0 : Fin 1))
          hfirst hprecision hbudget arity colors centers).trans (mul_le_mul_of_nonneg_right hs he)
open _root_.P2M9e1cfc64 renaming h398 → _p2mH398
end
open _root_.P2M9e1cfc64 renaming h394 → _p2mH394
open _root_.P2M9e1cfc64 renaming h398 → _p2mH398
end CurrentAFT.RationalRootGroupProgram
open _root_.P2M9e1cfc64 renaming h394 → _p2mH394
open _root_.P2M9e1cfc64 renaming h398 → _p2mH398
end
open _root_.P2M9e1cfc64 renaming h398 → _p2mH398
open _root_.P2M9e1cfc64 renaming h394 → _p2mH394
section
namespace CurrentAFT.CurrentRootSourceNatural
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
  CurrentGroupSourcePadding GroupSourcePadding CurrentRectangleIndex
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h63 (security : ℕ) (color : Fin (colors security)) :
    (rootEquiv security color).val = color.val := by
  have h (q : ℕ) [NeZero q] (point : Fin q) : ((ZMod.finEquiv q) point).val = point.val := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => rfl
  exact h (Parameters.modulus security) (paletteEquiv security color)
open _root_.P2M9e1cfc64 renaming h63 → _p2mH63
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h64 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged)
    (input : Input (colors security) (safe security) (groupKind selection tagged group)) :
    RationalRootGroupProgram.sourceNatural selection tagged group (groupEquiv selection tagged group input) =
      fun slot => (encode (colors security) (colors_pos security) (safe security)
        (groupKind selection tagged group) input slot).val := by
  rcases group with (primary | ordinary) | kept
  · dsimp only [groupKind, GroupSourcePadding.Input] at input
    rcases input with ⟨roots, control⟩
    funext slot
    fin_cases slot
    · change (rootEquiv security (roots 0)).val = (roots 0).val
      exact _p2mH63 security _
    · change (rootEquiv security (roots 1)).val = (roots 1).val
      exact _p2mH63 security _
    · rfl
  · dsimp only [groupKind, GroupSourcePadding.Input] at input
    rcases input with ⟨roots, control⟩
    funext slot
    fin_cases slot
    · change (rootEquiv security (roots 0)).val = (roots 0).val
      exact _p2mH63 security _
    · rfl
    · rfl
  · dsimp only [groupKind, GroupSourcePadding.Input] at input
    rcases input with ⟨roots, control⟩
    funext slot
    fin_cases slot
    · change (rootEquiv security (roots 0)).val = (roots 0).val
      exact _p2mH63 security _
    · rfl
    · rfl
open _root_.P2M9e1cfc64 renaming h64 → _p2mH64
end CurrentAFT.CurrentRootSourceNatural
open _root_.P2M9e1cfc64 renaming h63 → _p2mH63
open _root_.P2M9e1cfc64 renaming h64 → _p2mH64
end
open _root_.P2M9e1cfc64 renaming h64 → _p2mH64
open _root_.P2M9e1cfc64 renaming h63 → _p2mH63
section
namespace CurrentAFT.RationalFamilyWordProduct
open AFT ActualControls ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalFamilyWordProduct.wordProductFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h211 (security order count : ℕ) (families : Fin count → BackgroundFamilies.ActualFamily security order) :
    current order count (fun index arity => (families index arity).val) =
      fun arity => ((∏ index, families index) arity).val := by
  induction count with
  | zero => simpa only [current, Fin.prod_univ_zero] using _p2mH208 (ProposalPrimary.primaryLaw security) (bodyReference security) order
  | succ count ih =>
    rw [current, ih, _p2mH195, Fin.prod_univ_succ]
    have hm : (∏ index : Fin count, families index.succ) * families 0 =
        families 0 * (∏ index : Fin count, families index.succ) := mul_comm _ _
    change (fun arity => (((∏ index : Fin count, families index.succ) * families 0) arity).val) =
      (fun arity => ((families 0 * (∏ index : Fin count, families index.succ)) arity).val)
    rw [hm]
open _root_.P2M9e1cfc64 renaming h211 → _p2mH211
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h214 (security order count : ℕ) (tables : Fin count → Table ℚ ℕ ℕ order) :
    RationalActualFamilyApproximation.interpret security order (current order count tables) =
      current order count (fun index => RationalActualFamilyApproximation.interpret security order (tables index)) := by
  induction count with
  | zero =>
    unfold RationalActualFamilyApproximation.interpret current
    rw [_p2mH210, _p2mH203]
  | succ count ih =>
    rw [current, _p2mH150, ih]
    rfl
open _root_.P2M9e1cfc64 renaming h214 → _p2mH214
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h212 {Primary Body : Type*} (order count : ℕ) (tables : Fin count → Table ℝ Primary Body order)
    (bound scale : ℝ) (hb : 0 ≤ bound) (hs : 1 ≤ scale)
    (hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * bound ≤ scale)
    (htable : ∀ index arity colors centers, |tables index arity colors centers| ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary) (centers : Fin arity.val.2.val → Body) :
    |current order count tables arity colors centers| ≤ scale^count := by
  induction count generalizing arity colors centers with
  | zero => simpa only [current, pow_zero] using _p2mH209 order arity colors centers
  | succ count ih =>
    have ht := ih (fun index => tables index.succ) (fun index => htable index.succ)
    have h := _p2mH196 order (current order count (fun index => tables index.succ)) (tables 0)
      (scale^count) bound (by positivity) hb ht (htable 0) arity colors centers
    simp only [Fintype.card_eq_nat_card] at h
    apply h.trans
    have hm := mul_le_mul_of_nonneg_left hscale (pow_nonneg (by linarith : 0 ≤ scale) count)
    rw [pow_succ scale count]
    convert hm using 1
    ring
open _root_.P2M9e1cfc64 renaming h212 → _p2mH212
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h213 {Primary Body : Type*} (order count : ℕ) (tables computed : Fin count → Table ℝ Primary Body order)
    (bound error scale : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hs : 1 ≤ scale)
    (hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * (bound + error + 1) ≤ scale)
    (htable : ∀ index arity colors centers, |tables index arity colors centers| ≤ bound)
    (herror : ∀ index arity colors centers, |computed index arity colors centers - tables index arity colors centers| ≤ error)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary) (centers : Fin arity.val.2.val → Body) :
    |current order count computed arity colors centers - current order count tables arity colors centers| ≤
      count * error * scale^count := by
  have hn : 0 ≤ (Nat.card (TruncatedArity order) : ℝ)^2 := sq_nonneg _
  have hbase : (Nat.card (TruncatedArity order) : ℝ)^2 * bound ≤ scale :=
    (mul_le_mul_of_nonneg_left (show bound ≤ bound+error+1 by linarith) hn).trans hscale
  have hstep : (Nat.card (TruncatedArity order) : ℝ)^2 * (bound+error) ≤ scale :=
    (mul_le_mul_of_nonneg_left (show bound+error ≤ bound+error+1 by linarith) hn).trans hscale
  have hcount : (Nat.card (TruncatedArity order) : ℝ)^2 ≤ scale := by
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ bound+error+1 by linarith) hn
    rw [mul_one] at h
    exact h.trans hscale
  induction count generalizing arity colors centers with
  | zero => simp only [current, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ count ih =>
    have ht := _p2mH212 order count (fun index => tables index.succ) bound scale hb hs hbase (fun index => htable index.succ)
    have hi := ih (fun index => tables index.succ) (fun index => computed index.succ)
      (fun index => htable index.succ) (fun index => herror index.succ)
    have h := _p2mH198 order (current order count (fun index => tables index.succ))
      (current order count (fun index => computed index.succ)) (tables 0) (computed 0)
      (scale^count) bound (count*error*scale^count) error (by positivity) hb (by positivity) he
      ht (htable 0) hi (herror 0) arity colors centers
    simp only [Fintype.card_eq_nat_card] at h
    apply h.trans
    have hfirst := mul_le_mul_of_nonneg_left hstep (show 0 ≤ (count : ℝ)*error*scale^count by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hcount (show 0 ≤ error*scale^count by positivity)
    calc
      _ = ((count : ℝ)*error*scale^count) * ((Nat.card (TruncatedArity order) : ℝ)^2*(bound+error)) +
          (error*scale^count) * (Nat.card (TruncatedArity order) : ℝ)^2 := by ring
      _ ≤ ((count : ℝ)*error*scale^count)*scale + (error*scale^count)*scale := add_le_add hfirst hsecond
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one, pow_succ]; ring
open _root_.P2M9e1cfc64 renaming h213 → _p2mH213
end
open _root_.P2M9e1cfc64 renaming h211 → _p2mH211
open _root_.P2M9e1cfc64 renaming h212 → _p2mH212
open _root_.P2M9e1cfc64 renaming h213 → _p2mH213
open _root_.P2M9e1cfc64 renaming h214 → _p2mH214
end CurrentAFT.RationalFamilyWordProduct
open _root_.P2M9e1cfc64 renaming h211 → _p2mH211
open _root_.P2M9e1cfc64 renaming h212 → _p2mH212
open _root_.P2M9e1cfc64 renaming h213 → _p2mH213
open _root_.P2M9e1cfc64 renaming h214 → _p2mH214
end
open _root_.P2M9e1cfc64 renaming h212 → _p2mH212
open _root_.P2M9e1cfc64 renaming h214 → _p2mH214
open _root_.P2M9e1cfc64 renaming h213 → _p2mH213
open _root_.P2M9e1cfc64 renaming h211 → _p2mH211
namespace CurrentAFT.CurrentRootSourceNatural
end CurrentAFT.CurrentRootSourceNatural
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT ActualBlockFock TaggedSelection PairedRootPlacement CurrentGroupSourcePadding
  CurrentRootOrdering CurrentRootSlotIndex CurrentRectangleIndex GroupSourcePadding RationalRootGroupProgram
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h321 {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (group : ActiveGroup selection tagged) : nativeKind (nativeRole selection tagged group) = groupKind selection tagged group := by
  rcases group with (primary | ordinary) | kept
  · rfl
  · rfl
  · rcases hk : kept.val.val with leg | (center | queue) <;> simp only [nativeRole, hk, nativeKind, groupKind]
open _root_.P2M9e1cfc64 renaming h321 → _p2mH321
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h353 (security : ℕ) (role : LocalRole) (word : Fin 3 → Fin (colors security)) :
    validGroup security role (fun slot => (word slot).val) ↔
      GroupSourcePadding.Valid (colors security) (safe security) (nativeKind role) word := by
  cases role <;> rfl
open _root_.P2M9e1cfc64 renaming h353 → _p2mH353
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h343 (security groups : ℕ) (word : Fin groups → Fin 3 → Fin (colors security)) :
    sourceWord security groups
      ((tupleEquiv (colors security) (groups*3) (colors_pos security))
        (fun index => word (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2)) =
      fun group slot => (word group slot).val := by
  funext group slot
  change (WeightCoordinates.tupleDecode (colors security) (colors_pos security) (groups*3)
    (WeightCoordinates.tupleCode (colors security) (groups*3)
      (fun index => (word (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2).val))
      (finProdFinEquiv (group, slot))).val = (word group slot).val
  rw [WeightCoordinates.tupleDecode_code]
  simp only [Equiv.symm_apply_apply]
open _root_.P2M9e1cfc64 renaming h343 → _p2mH343
section NativeEncoding
variable {Group : Type*} [Fintype Group] [DecidableEq Group]
set_option maxRecDepth 8192
omit [Fintype Group] [DecidableEq Group] in
theorem _root_.P2M9e1cfc64.h341 (security count : ℕ) (kind : Group → Kind) (order : Fin count ≃ Group)
    (source : Source (colors security) (safe security) kind) :
    sourceWord security count (indexEncode (colors security) (colors_pos security) (safe security) kind count order source) =
      fun index slot => (GroupSourcePadding.encode (colors security) (colors_pos security) (safe security)
        (kind (order index)) (source (order index)) slot).val := by
  exact _p2mH343 security count (fun index =>
    GroupSourcePadding.encode (colors security) (colors_pos security) (safe security) (kind (order index)) (source (order index)))
open _root_.P2M9e1cfc64 renaming h341 → _p2mH341
end NativeEncoding
open _root_.P2M9e1cfc64 renaming h341 → _p2mH341
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedSourceFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedSourceSumDecidableEq
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h342 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source) =
      fun index => RationalRootGroupProgram.sourceNatural selection tagged (ordering selection tagged index)
        (source (ordering selection tagged index)) := by
  rw [sourceIndex, _p2mH341]
  funext index
  have h := _p2mH64 selection tagged (ordering selection tagged index)
    (((sourceEquiv selection tagged).symm source) (ordering selection tagged index))
  have hs := congrFun ((sourceEquiv selection tagged).apply_symm_apply source) (ordering selection tagged index)
  change groupEquiv selection tagged (ordering selection tagged index)
    (((sourceEquiv selection tagged).symm source) (ordering selection tagged index)) = _ at hs
  rw [hs] at h
  exact h.symm
open _root_.P2M9e1cfc64 renaming h342 → _p2mH342
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h355 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    Valid security (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) := by
  rw [sourceIndex, _p2mH341]
  intro index
  rw [_p2mH353]
  simp only [actualMetadata, _p2mH321]
  exact encode_valid (colors security) (colors_pos security) (safe security) _ _
open _root_.P2M9e1cfc64 renaming h355 → _p2mH355
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h317 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (index : Fin ((colors security)^((groupCount selection tagged)*3)))
    (group : ActiveGroup selection tagged) (slot : Fin 3) :
    (((indexEquiv (colors security) (colors_pos security) (groupCount selection tagged)
      (ordering selection tagged)).symm index) group slot).val =
      sourceWord security (groupCount selection tagged) index ((ordering selection tagged).symm group) slot := rfl
open _root_.P2M9e1cfc64 renaming h317 → _p2mH317
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h354 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin ((colors security)^((groupCount selection tagged)*3))) :
    Valid security (actualMetadata selection tagged) (sourceWord security (groupCount selection tagged) index) ↔
      ∀ group, GroupSourcePadding.Valid (colors security) (safe security) (groupKind selection tagged group)
        (((indexEquiv (colors security) (colors_pos security) (groupCount selection tagged)
          (ordering selection tagged)).symm index) group) := by
  constructor
  · intro h group
    have hg := h ((ordering selection tagged).symm group)
    have hw : (fun slot => (((indexEquiv (colors security) (colors_pos security) (groupCount selection tagged)
        (ordering selection tagged)).symm index) group slot).val) =
        sourceWord security (groupCount selection tagged) index ((ordering selection tagged).symm group) := by
      funext slot
      exact _p2mH317 selection tagged index group slot
    rw [← hw, _p2mH353] at hg
    simpa only [actualMetadata, _p2mH321, Equiv.apply_symm_apply] using hg
  · intro h groupIndex
    have hg := h (ordering selection tagged groupIndex)
    have hw : (fun slot => (((indexEquiv (colors security) (colors_pos security) (groupCount selection tagged)
        (ordering selection tagged)).symm index) (ordering selection tagged groupIndex) slot).val) =
        sourceWord security (groupCount selection tagged) index groupIndex := by
      funext slot
      rw [_p2mH317, Equiv.symm_apply_apply]
    rw [← hw, _p2mH353]
    simpa only [actualMetadata, _p2mH321] using hg
open _root_.P2M9e1cfc64 renaming h354 → _p2mH354
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h316 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin ((colors security)^((groupCount selection tagged)*3))) :
    CurrentGroupSourcePadding.decode selection tagged (keptOrdering selection tagged) index = none ↔
      ¬Valid security (actualMetadata selection tagged) (sourceWord security (groupCount selection tagged) index) := by
  rw [_p2mH354]
  change (sourceDecode (colors security) (safe security) (groupKind selection tagged)
    ((indexEquiv (colors security) (colors_pos security) (groupCount selection tagged)
      (ordering selection tagged)).symm index)).map (sourceEquiv selection tagged) = none ↔ _
  by_cases h : ∀ group, GroupSourcePadding.Valid (colors security) (safe security) (groupKind selection tagged group)
      (((indexEquiv (colors security) (colors_pos security) (groupCount selection tagged)
        (ordering selection tagged)).symm index) group)
  · rw [GroupSourcePadding.sourceDecode, dif_pos h]
    constructor
    · intro hnone; cases hnone
    · intro hnot; exact False.elim (hnot h)
  · rw [GroupSourcePadding.sourceDecode, dif_neg h]
    exact ⟨fun _ => h, fun _ => rfl⟩
open _root_.P2M9e1cfc64 renaming h316 → _p2mH316
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h315 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin ((colors security)^((groupCount selection tagged)*3)))
    (source : PairedRootInput.GroupInput selection tagged) :
    CurrentGroupSourcePadding.decode selection tagged (keptOrdering selection tagged) index = some source ↔
      index = sourceIndex selection tagged source := by
  unfold CurrentGroupSourcePadding.decode
  constructor
  · intro h
    obtain ⟨native, hn, hs⟩ := Option.map_eq_some_iff.mp h
    have heq : native = (sourceEquiv selection tagged).symm source := (sourceEquiv selection tagged).apply_eq_iff_eq_symm_apply.mp hs
    subst native
    exact (_p2mH87 (colors security) (colors_pos security) (safe security)
      (groupKind selection tagged) (groupCount selection tagged) (ordering selection tagged) index _).mp hn
  · intro h
    subst index
    have hn := (_p2mH87 (colors security) (colors_pos security) (safe security)
      (groupKind selection tagged) (groupCount selection tagged) (ordering selection tagged)
      (sourceIndex selection tagged source) ((sourceEquiv selection tagged).symm source)).mpr rfl
    change (indexDecode (colors security) (colors_pos security) (safe security) (groupKind selection tagged)
      (groupCount selection tagged) (ordering selection tagged) (sourceIndex selection tagged source)).map
      (sourceEquiv selection tagged) = some source
    rw [hn]
    exact congrArg some ((sourceEquiv selection tagged).apply_symm_apply source)
open _root_.P2M9e1cfc64 renaming h315 → _p2mH315
end
open _root_.P2M9e1cfc64 renaming h315 → _p2mH315
open _root_.P2M9e1cfc64 renaming h316 → _p2mH316
open _root_.P2M9e1cfc64 renaming h317 → _p2mH317
open _root_.P2M9e1cfc64 renaming h342 → _p2mH342
open _root_.P2M9e1cfc64 renaming h354 → _p2mH354
open _root_.P2M9e1cfc64 renaming h355 → _p2mH355
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M9e1cfc64 renaming h315 → _p2mH315
open _root_.P2M9e1cfc64 renaming h316 → _p2mH316
open _root_.P2M9e1cfc64 renaming h317 → _p2mH317
open _root_.P2M9e1cfc64 renaming h321 → _p2mH321
open _root_.P2M9e1cfc64 renaming h341 → _p2mH341
open _root_.P2M9e1cfc64 renaming h342 → _p2mH342
open _root_.P2M9e1cfc64 renaming h343 → _p2mH343
open _root_.P2M9e1cfc64 renaming h353 → _p2mH353
open _root_.P2M9e1cfc64 renaming h354 → _p2mH354
open _root_.P2M9e1cfc64 renaming h355 → _p2mH355
end
open _root_.P2M9e1cfc64 renaming h316 → _p2mH316
open _root_.P2M9e1cfc64 renaming h342 → _p2mH342
open _root_.P2M9e1cfc64 renaming h315 → _p2mH315
open _root_.P2M9e1cfc64 renaming h341 → _p2mH341
open _root_.P2M9e1cfc64 renaming h343 → _p2mH343
open _root_.P2M9e1cfc64 renaming h353 → _p2mH353
open _root_.P2M9e1cfc64 renaming h355 → _p2mH355
open _root_.P2M9e1cfc64 renaming h317 → _p2mH317
open _root_.P2M9e1cfc64 renaming h321 → _p2mH321
open _root_.P2M9e1cfc64 renaming h354 → _p2mH354
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT ActualBlockFock TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRootSlotIndex CurrentRectangleIndex GroupSourcePadding RationalRootGroupProgram CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedSignedFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedSignedVertexDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference rootLaw
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h339 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged)
    (root : CurrentRootSlotIndex.Slot selection tagged) :
    RationalRootGroupProgram.sourceNatural selection tagged root.fst (source root.fst)
      (slotNumber selection tagged root).castSucc = ((source root.fst).1 root.snd).val := by
  rcases root with ⟨(primary | ordinary) | kept, slot⟩
  · change Fin 2 at slot
    fin_cases slot <;> rfl
  · change Fin 1 at slot
    have hs : slot = 0 := Subsingleton.elim _ _
    subst slot
    rfl
  · change Fin 1 at slot
    have hs : slot = 0 := Subsingleton.elim _ _
    subst slot
    rfl
open _root_.P2M9e1cfc64 renaming h339 → _p2mH339
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h338 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged)
    (root : CurrentRootSlotIndex.Slot selection tagged) :
    sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
      ((ordering selection tagged).symm root.fst) (slotNumber selection tagged root).castSucc =
      ((source root.fst).1 root.snd).val := by
  rw [_p2mH342]
  try dsimp only
  rw [Equiv.apply_symm_apply, _p2mH339]
open _root_.P2M9e1cfc64 renaming h338 → _p2mH338
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h334 {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    signed security bits (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) =
      RootSignedMassProgram.weightedEntry security bits tagged.card (fun index => (sortedOutput selection tagged source index).val) := by
  unfold signed
  congr 1
  funext index
  simp only [actualMetadata, CurrentRootSlotIndex.taggedSlots, _p2mH62]
  exact _p2mH338 selection tagged source _
open _root_.P2M9e1cfc64 renaming h334 → _p2mH334
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h335 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (source : PairedRootInput.GroupInput selection tagged) :
    (rootLaw security).expectation (fun roots => ∏ index,
      ((if roots (sortedLabels tagged layout index) = sortedOutput selection tagged source index then (1 : ℝ) else 0) -
        (rootReference security).weight (sortedOutput selection tagged source index))) =
      RootWeightedSynthesis.weightedCoefficient selection tagged layout source := by
  apply congrArg (rootLaw security).expectation
  funext roots
  let test := fun tag : tagged =>
    ((if roots (layout tag.val) = (source (tagEmbedding selection tagged tag).fst).1 (tagEmbedding selection tagged tag).snd then (1 : ℝ) else 0) -
      (rootReference security).weight ((source (tagEmbedding selection tagged tag).fst).1 (tagEmbedding selection tagged tag).snd))
  change (∏ index : Fin tagged.card, test (tagOrdering tagged index)) =
    ∏ index : Fin tagged.card, test (tagged.equivFin.symm index)
  exact (tagOrdering tagged).prod_comp test |>.trans (tagged.equivFin.symm.prod_comp test).symm
open _root_.P2M9e1cfc64 renaming h335 → _p2mH335
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h333 {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (hroom : tagged.card ≤ Parameters.bodySize security) (source : PairedRootInput.GroupInput selection tagged) :
    |(signed security bits (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) : ℝ) -
      RootWeightedSynthesis.weightedCoefficient selection tagged layout source| ≤ (4 * tagged.card : ℕ) / (2 : ℝ)^bits := by
  letI : DecidableEq (Fin tagged.card) := instDecidableEqFin _
  rw [_p2mH334]
  have h := _p2mH528 security bits tagged.card hroom
    (sortedLabels tagged layout) (sortedOutput selection tagged source)
  have hmass := _p2mH519 security tagged.card
    (sortedLabels tagged layout) (sortedOutput selection tagged source)
  rw [FiniteDist.expectation_map] at hmass
  have heq := hmass.trans (_p2mH335 selection tagged layout source)
  rw [heq] at h
  exact h
open _root_.P2M9e1cfc64 renaming h333 → _p2mH333
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h356 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (source : PairedRootInput.GroupInput selection tagged) :
    |RootWeightedSynthesis.weightedCoefficient selection tagged layout source| ≤ 1 := by
  apply _p2mH48
  intro roots
  rw [Finset.abs_prod]
  apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
  intro index _
  have hlo := (rootReference security).nonneg (RootWeightedSynthesis.taggedOutput selection tagged source index)
  have hhi := (rootReference security).atom_le_one (RootWeightedSynthesis.taggedOutput selection tagged source index)
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
open _root_.P2M9e1cfc64 renaming h356 → _p2mH356
end
open _root_.P2M9e1cfc64 renaming h333 → _p2mH333
open _root_.P2M9e1cfc64 renaming h334 → _p2mH334
open _root_.P2M9e1cfc64 renaming h335 → _p2mH335
open _root_.P2M9e1cfc64 renaming h338 → _p2mH338
open _root_.P2M9e1cfc64 renaming h339 → _p2mH339
open _root_.P2M9e1cfc64 renaming h356 → _p2mH356
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M9e1cfc64 renaming h333 → _p2mH333
open _root_.P2M9e1cfc64 renaming h334 → _p2mH334
open _root_.P2M9e1cfc64 renaming h335 → _p2mH335
open _root_.P2M9e1cfc64 renaming h338 → _p2mH338
open _root_.P2M9e1cfc64 renaming h339 → _p2mH339
open _root_.P2M9e1cfc64 renaming h356 → _p2mH356
end
open _root_.P2M9e1cfc64 renaming h338 → _p2mH338
open _root_.P2M9e1cfc64 renaming h356 → _p2mH356
open _root_.P2M9e1cfc64 renaming h339 → _p2mH339
open _root_.P2M9e1cfc64 renaming h333 → _p2mH333
open _root_.P2M9e1cfc64 renaming h334 → _p2mH334
open _root_.P2M9e1cfc64 renaming h335 → _p2mH335
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRootSlotIndex CycleRootExpansion
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedSigmaDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedProdDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h345 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (root : Slot selection tagged) :
    (∃ index, (actualMetadata selection tagged).taggedSlots index =
      ((ordering selection tagged).symm root.fst, slotNumber selection tagged root)) ↔
      rootEmbedding selection tagged root ∈ tagged := by
  constructor
  · rintro ⟨index, h⟩
    change CurrentRootSlotIndex.tagPosition selection tagged (ordering selection tagged)
      (tagOrdering tagged index) = _ at h
    rw [_p2mH62] at h
    have he := congrArg finProdFinEquiv h
    change CurrentRootSlotIndex.encode selection tagged (ordering selection tagged)
      (tagEmbedding selection tagged (tagOrdering tagged index)) =
      CurrentRootSlotIndex.encode selection tagged (ordering selection tagged) root at he
    have hr : tagEmbedding selection tagged (tagOrdering tagged index) = root := by
      have hd := congrArg (CurrentRootSlotIndex.decode selection tagged (ordering selection tagged)) he
      simpa only [decode_encode, Option.some.injEq] using hd
    rw [← hr, tag_image]
    exact (tagOrdering tagged index).property
  · intro h
    let tag : tagged := ⟨rootEmbedding selection tagged root, h⟩
    have hr : tagEmbedding selection tagged tag = root :=
      (rootEmbedding selection tagged).injective (tag_image selection tagged tag)
    refine ⟨(tagOrdering tagged).symm tag, ?_⟩
    change CurrentRootSlotIndex.tagPosition selection tagged (ordering selection tagged)
      (tagOrdering tagged ((tagOrdering tagged).symm tag)) = _
    rw [Equiv.apply_symm_apply, _p2mH62, hr]
open _root_.P2M9e1cfc64 renaming h345 → _p2mH345
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h336 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (root : Slot selection tagged) :
    root ∈ Finset.univ.map (PairedRootInput.sourceEmbedding selection tagged) ↔
      rootEmbedding selection tagged root ∈ tagged := by
  constructor
  · intro h
    obtain ⟨index, _, he⟩ := Finset.mem_map.mp h
    rw [← he]
    change rootEmbedding selection tagged
      (tagEmbedding selection tagged (tagged.equivFin.symm index)) ∈ tagged
    rw [tag_image]
    exact (tagged.equivFin.symm index).property
  · intro h
    let tag : tagged := ⟨rootEmbedding selection tagged root, h⟩
    refine Finset.mem_map.mpr ⟨tagged.equivFin tag, Finset.mem_univ _, ?_⟩
    change tagEmbedding selection tagged (tagged.equivFin.symm (tagged.equivFin tag)) = root
    rw [Equiv.symm_apply_apply]
    exact (rootEmbedding selection tagged).injective (tag_image selection tagged tag)
open _root_.P2M9e1cfc64 renaming h336 → _p2mH336
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h328 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (root : Slot selection tagged) :
    rootActive (nativeRole selection tagged root.fst) (slotNumber selection tagged root) := by
  rcases root with ⟨(primary | ordinary) | kept, slot⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
open _root_.P2M9e1cfc64 renaming h328 → _p2mH328
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h322 {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged)
    (root : Slot selection tagged) :
    (if rootActive ((actualMetadata selection tagged).roles ((ordering selection tagged).symm root.fst))
        (slotNumber selection tagged root) ∧ ¬∃ index,
          (actualMetadata selection tagged).taggedSlots index =
            ((ordering selection tagged).symm root.fst, slotNumber selection tagged root)
      then RootSignedMassProgram.referenceEntry security bits
        (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
          ((ordering selection tagged).symm root.fst) (slotNumber selection tagged root).castSucc) else 1) =
      untaggedFactor bits selection tagged source root := by
  rw [_p2mH338]
  have ha : rootActive ((actualMetadata selection tagged).roles ((ordering selection tagged).symm root.fst))
      (slotNumber selection tagged root) := by
    change rootActive (nativeRole selection tagged (ordering selection tagged ((ordering selection tagged).symm root.fst))) _
    rw [Equiv.apply_symm_apply]
    exact _p2mH328 selection tagged root
  unfold untaggedFactor
  by_cases ht : rootEmbedding selection tagged root ∈ tagged <;> simp only [_p2mH345, ha, ht, not_true_eq_false,
    not_false_eq_true, true_and, ite_true, ite_false]
open _root_.P2M9e1cfc64 renaming h322 → _p2mH322
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h352 {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    untagged security bits (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) =
      ∏ root : Slot selection tagged, untaggedFactor bits selection tagged source root := by
  unfold untagged
  have hp := (ordering selection tagged).symm.prod_comp (fun group => ∏ slot : Fin 2,
    if rootActive ((actualMetadata selection tagged).roles group) slot ∧ ¬∃ tag,
      (actualMetadata selection tagged).taggedSlots tag = (group, slot) then
        RootSignedMassProgram.referenceEntry security bits
          (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source) group slot.castSucc) else (1 : ℚ))
  trans ∏ group : ActiveGroup selection tagged, ∏ slot : Fin 2,
    if rootActive ((actualMetadata selection tagged).roles ((ordering selection tagged).symm group)) slot ∧ ¬∃ tag,
      (actualMetadata selection tagged).taggedSlots tag = ((ordering selection tagged).symm group, slot) then
        RootSignedMassProgram.referenceEntry security bits
          (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
            ((ordering selection tagged).symm group) slot.castSucc) else 1
  · convert hp.symm using 1
    apply Finset.prod_congr rfl
    intro group _
    apply Finset.prod_congr rfl
    intro slot _
    split_ifs <;> rfl
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro group _
  rcases group with (primary | ordinary) | kept
  · change (∏ slot : Fin 2, _) = ∏ slot : Fin 2, _
    apply Finset.prod_congr rfl
    intro slot _
    exact _p2mH322 bits selection tagged source ⟨.inl (.inl primary), slot⟩
  · change (∏ slot : Fin 2, _) = ∏ slot : Fin 1, _
    rw [Fin.prod_univ_two, Fin.prod_univ_one]
    have hf := _p2mH322 bits selection tagged source ⟨.inl (.inr ordinary), (0 : Fin 1)⟩
    have hinactive : ¬rootActive ((actualMetadata selection tagged).roles
      ((ordering selection tagged).symm (.inl (.inr ordinary)))) (1 : Fin 2) := by
      simp [actualMetadata, nativeRole, rootActive]
    simpa only [slotNumber,hinactive,false_and,ite_false,mul_one] using hf
  · change (∏ slot : Fin 2, _) = ∏ slot : Fin 1, _
    rw [Fin.prod_univ_two, Fin.prod_univ_one]
    have hf := _p2mH322 bits selection tagged source ⟨.inr kept, (0 : Fin 1)⟩
    have hinactive : ¬rootActive ((actualMetadata selection tagged).roles
      ((ordering selection tagged).symm (.inr kept))) (1 : Fin 2) := by
      simp only [actualMetadata, Equiv.apply_symm_apply, rootActive, nativeRole]
      rcases kept.val.val with leg | (center | queue) <;> simp
    simpa only [slotNumber,hinactive,false_and,ite_false,mul_one] using hf
open _root_.P2M9e1cfc64 renaming h352 → _p2mH352
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h349 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    RootWeightedSynthesis.untaggedWeight selection tagged source =
      ∏ root : Slot selection tagged, if rootEmbedding selection tagged root ∈ tagged then 1 else
        (rootReference security).weight ((source root.fst).1 root.snd) := by
  unfold RootWeightedSynthesis.untaggedWeight
  have hc : (Finset.univ.map (PairedRootInput.sourceEmbedding selection tagged))ᶜ =
      Finset.univ.filter (fun root => rootEmbedding selection tagged root ∉ tagged) := by
    ext root
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, _p2mH336]
  rw [hc, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro root _
  by_cases ht : rootEmbedding selection tagged root ∈ tagged <;> simp only [ht, not_true_eq_false,
    not_false_eq_true, ite_true, ite_false]
open _root_.P2M9e1cfc64 renaming h349 → _p2mH349
end
open _root_.P2M9e1cfc64 renaming h322 → _p2mH322
open _root_.P2M9e1cfc64 renaming h328 → _p2mH328
open _root_.P2M9e1cfc64 renaming h336 → _p2mH336
open _root_.P2M9e1cfc64 renaming h345 → _p2mH345
open _root_.P2M9e1cfc64 renaming h349 → _p2mH349
open _root_.P2M9e1cfc64 renaming h352 → _p2mH352
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M9e1cfc64 renaming h322 → _p2mH322
open _root_.P2M9e1cfc64 renaming h328 → _p2mH328
open _root_.P2M9e1cfc64 renaming h336 → _p2mH336
open _root_.P2M9e1cfc64 renaming h345 → _p2mH345
open _root_.P2M9e1cfc64 renaming h349 → _p2mH349
open _root_.P2M9e1cfc64 renaming h352 → _p2mH352
end
open _root_.P2M9e1cfc64 renaming h328 → _p2mH328
open _root_.P2M9e1cfc64 renaming h345 → _p2mH345
open _root_.P2M9e1cfc64 renaming h352 → _p2mH352
open _root_.P2M9e1cfc64 renaming h349 → _p2mH349
open _root_.P2M9e1cfc64 renaming h336 → _p2mH336
open _root_.P2M9e1cfc64 renaming h322 → _p2mH322
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentRootSlotIndex CycleRootExpansion
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedBoundsFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedBoundsSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedUntaggedBoundsSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h329 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    Fintype.card (Slot selection tagged) ≤ 2 * groupCount selection tagged := by
  have hi : Function.Injective (CurrentRootSlotIndex.encode selection tagged (ordering selection tagged)) := by
    intro first second h
    have hd := congrArg (CurrentRootSlotIndex.decode selection tagged (ordering selection tagged)) h
    simpa only [decode_encode, Option.some.injEq] using hd
  have h := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_fin, Nat.mul_comm] using h
open _root_.P2M9e1cfc64 renaming h329 → _p2mH329
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h347 {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged)
    (root : Slot selection tagged) :
    0 ≤ (untaggedFactor bits selection tagged source root : ℝ) ∧
      (untaggedFactor bits selection tagged source root : ℝ) ≤ 1 := by
  unfold untaggedFactor
  split_ifs
  · norm_num
  · exact _p2mH520 security bits _
open _root_.P2M9e1cfc64 renaming h347 → _p2mH347
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h350 {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    0 ≤ (untagged security bits (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) : ℝ) ∧
    (untagged security bits (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) : ℝ) ≤ 1 := by
  rw [_p2mH352, Rat.cast_prod]
  exact ⟨Finset.prod_nonneg (fun root _ => (_p2mH347 bits selection tagged source root).1),
    Finset.prod_le_one (fun root _ => (_p2mH347 bits selection tagged source root).1)
      (fun root _ => (_p2mH347 bits selection tagged source root).2)⟩
open _root_.P2M9e1cfc64 renaming h350 → _p2mH350
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h348 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    0 ≤ RootWeightedSynthesis.untaggedWeight selection tagged source ∧
      RootWeightedSynthesis.untaggedWeight selection tagged source ≤ 1 := by
  rw [_p2mH349]
  have hb (root : Slot selection tagged) :
      0 ≤ (if rootEmbedding selection tagged root ∈ tagged then (1 : ℝ) else
        (rootReference security).weight ((source root.fst).1 root.snd)) ∧
      (if rootEmbedding selection tagged root ∈ tagged then (1 : ℝ) else
        (rootReference security).weight ((source root.fst).1 root.snd)) ≤ 1 := by
    split_ifs
    · norm_num
    · exact ⟨FiniteDist.nonneg _ _, FiniteDist.atom_le_one _ _⟩
  exact ⟨Finset.prod_nonneg (fun root _ => (hb root).1),
    Finset.prod_le_one (fun root _ => (hb root).1) (fun root _ => (hb root).2)⟩
open _root_.P2M9e1cfc64 renaming h348 → _p2mH348
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h351 {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    |(untagged security bits (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) : ℝ) -
      RootWeightedSynthesis.untaggedWeight selection tagged source| ≤
      (4 * groupCount selection tagged : ℕ) * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH352, Rat.cast_prod, _p2mH349]
  let first := fun root : Slot selection tagged => (untaggedFactor bits selection tagged source root : ℝ)
  let second := fun root : Slot selection tagged =>
    if rootEmbedding selection tagged root ∈ tagged then (1 : ℝ) else
      (rootReference security).weight ((source root.fst).1 root.snd)
  have hsecond (root : Slot selection tagged) : |second root| ≤ 1 := by
    dsimp only [second]
    split_ifs
    · norm_num
    · rw [abs_of_nonneg ((rootReference security).nonneg ((source root.fst).1 root.snd))]
      exact (rootReference security).atom_le_one _
  have hdiff (root : Slot selection tagged) : |first root - second root| ≤ 2 / (2 : ℝ)^bits := by
    dsimp only [first, second, untaggedFactor]
    split_ifs
    · simp only [Rat.cast_one, sub_self, abs_zero]; positivity
    · exact _p2mH522 security bits _
  have h := _p2mH464 Finset.univ first second 1
    (2 / (2 : ℝ)^bits) (by norm_num) (by positivity)
    (fun root _ => (abs_of_nonneg (_p2mH347 bits selection tagged source root).1).trans_le
      (_p2mH347 bits selection tagged source root).2)
    (fun root _ => hsecond root) (fun root _ => hdiff root)
  simp only [Finset.card_univ, one_pow, mul_one] at h
  refine h.trans ?_
  have hc : (Fintype.card (Slot selection tagged) : ℝ) ≤ 2 * groupCount selection tagged := by
    exact_mod_cast _p2mH329 selection tagged
  calc
    _ ≤ (2 * groupCount selection tagged : ℝ) * (2 / (2 : ℝ)^bits) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by push_cast; ring
open _root_.P2M9e1cfc64 renaming h351 → _p2mH351
end
open _root_.P2M9e1cfc64 renaming h329 → _p2mH329
open _root_.P2M9e1cfc64 renaming h347 → _p2mH347
open _root_.P2M9e1cfc64 renaming h348 → _p2mH348
open _root_.P2M9e1cfc64 renaming h350 → _p2mH350
open _root_.P2M9e1cfc64 renaming h351 → _p2mH351
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M9e1cfc64 renaming h329 → _p2mH329
open _root_.P2M9e1cfc64 renaming h347 → _p2mH347
open _root_.P2M9e1cfc64 renaming h348 → _p2mH348
open _root_.P2M9e1cfc64 renaming h350 → _p2mH350
open _root_.P2M9e1cfc64 renaming h351 → _p2mH351
end
open _root_.P2M9e1cfc64 renaming h348 → _p2mH348
open _root_.P2M9e1cfc64 renaming h347 → _p2mH347
open _root_.P2M9e1cfc64 renaming h350 → _p2mH350
open _root_.P2M9e1cfc64 renaming h351 → _p2mH351
open _root_.P2M9e1cfc64 renaming h329 → _p2mH329
section
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRectangleIndex RationalRootGroupProgram CycleRootExpansion ActualControls
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedControlFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedControlSafeDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h325 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin r) :
    ordering selection tagged (primaryGroup r s (keptIndices selection tagged).card index) = .inl (.inl index) := by
  apply (ordering selection tagged).apply_eq_iff_eq_symm_apply.mpr
  apply Fin.ext
  rfl
open _root_.P2M9e1cfc64 renaming h325 → _p2mH325
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h324 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin s) :
    ordering selection tagged (ordinaryGroup r s (keptIndices selection tagged).card index) = .inl (.inr index) := by
  apply (ordering selection tagged).apply_eq_iff_eq_symm_apply.mpr
  apply Fin.ext
  rfl
open _root_.P2M9e1cfc64 renaming h324 → _p2mH324
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h314 {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged) :
    control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
      (fun index => (sourceBody index).val.val)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) =
      WeightedPointKernelProgram.current security bits r s (fun index => (sourcePrimary index).val)
        (fun index => (sourceBody index).val.val)
        (fun index => (source (.inl (.inl index))).2.val) (fun index => (source (.inl (.inr index))).2.val.val) := by
  unfold control
  rw [_p2mH342]
  congr 1
  · funext index
    try dsimp only
    rw [_p2mH325]
    rfl
  · funext index
    try dsimp only
    rw [_p2mH324]
    rfl
open _root_.P2M9e1cfc64 renaming h314 → _p2mH314
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h313 {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
        (fun index => (sourceBody index).val.val)
        (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) : ℝ) -
      PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
        (fun group => (source group).2)| ≤ WeightedPointKernelProgram.errorConstant security r s * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH314]
  exact _p2mH547 security bits r s sourcePrimary sourceBody hprecision hbudget _ _
open _root_.P2M9e1cfc64 renaming h313 → _p2mH313
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h312 {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged) :
    |PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
      (fun group => (source group).2)| ≤ 1 := by
  exact _p2mH542 security sourcePrimary sourceBody _ _
open _root_.P2M9e1cfc64 renaming h312 → _p2mH312
end
open _root_.P2M9e1cfc64 renaming h312 → _p2mH312
open _root_.P2M9e1cfc64 renaming h313 → _p2mH313
open _root_.P2M9e1cfc64 renaming h314 → _p2mH314
open _root_.P2M9e1cfc64 renaming h324 → _p2mH324
open _root_.P2M9e1cfc64 renaming h325 → _p2mH325
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M9e1cfc64 renaming h312 → _p2mH312
open _root_.P2M9e1cfc64 renaming h313 → _p2mH313
open _root_.P2M9e1cfc64 renaming h314 → _p2mH314
open _root_.P2M9e1cfc64 renaming h324 → _p2mH324
open _root_.P2M9e1cfc64 renaming h325 → _p2mH325
end
open _root_.P2M9e1cfc64 renaming h324 → _p2mH324
open _root_.P2M9e1cfc64 renaming h313 → _p2mH313
open _root_.P2M9e1cfc64 renaming h325 → _p2mH325
open _root_.P2M9e1cfc64 renaming h312 → _p2mH312
open _root_.P2M9e1cfc64 renaming h314 → _p2mH314
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
theorem _root_.P2M9e1cfc64.h326 (security r s : ℕ) :
    0 ≤ WeightedPointKernelProgram.errorConstant security r s := by
  unfold WeightedPointKernelProgram.errorConstant RationalRootMassProgram.primaryErrorConstant
  positivity
open _root_.P2M9e1cfc64 renaming h326 → _p2mH326
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h331 (security r s count tags : ℕ) : 0 ≤ scalarError security r s count tags := by
  unfold scalarError
  have h := _p2mH326 security r s
  positivity
open _root_.P2M9e1cfc64 renaming h331 → _p2mH331
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h330 (security r s tags : ℕ) : 0 ≤ scalarBound security r s tags := by
  unfold scalarBound
  have h := _p2mH326 security r s
  positivity
open _root_.P2M9e1cfc64 renaming h330 → _p2mH330
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h346 (a b x y A B e f : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (he : 0 ≤ e) (_hf : 0 ≤ f) (hx : |x| ≤ A) (hb : |b| ≤ B)
    (ha : |a-x| ≤ e) (hy : |b-y| ≤ f) :
    |a*b-x*y| ≤ e*B+A*f := by
  calc
    _ = |(a-x)*b+x*(b-y)| := by congr 1; ring
    _ ≤ |a-x| * |b| + |x| * |b-y| := by simpa only [abs_mul] using abs_add_le ((a-x)*b) (x*(b-y))
    _ ≤ e*B+A*f := add_le_add (mul_le_mul ha hb (abs_nonneg _) he)
      (mul_le_mul hx hy (abs_nonneg _) hA)
open _root_.P2M9e1cfc64 renaming h346 → _p2mH346
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h332 {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (hroom : tagged.card ≤ Parameters.bodySize security)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(sourceScalar bits selection tagged sourcePrimary sourceBody source : ℝ) -
      actualScalar selection tagged layout sourcePrimary sourceBody source| ≤
      scalarError security r s (groupCount selection tagged) tagged.card * (1/(2:ℝ)^bits) := by
  let word := sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
  let a : ℝ := control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
    (fun index => (sourceBody index).val.val) word
  let b : ℝ := untagged security bits (actualMetadata selection tagged) word
  let c : ℝ := signed security bits (actualMetadata selection tagged) word
  let x := PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
    (fun group => (source group).2)
  let y := RootWeightedSynthesis.untaggedWeight selection tagged source
  let z := RootWeightedSynthesis.weightedCoefficient selection tagged layout source
  let epsilon : ℝ := 1/(2:ℝ)^bits
  let E := WeightedPointKernelProgram.errorConstant security r s
  have hE : 0 ≤ E := _p2mH326 security r s
  have he : 0 ≤ epsilon := by positivity
  have he1 : epsilon ≤ 1 := _p2mH168 bits
  have ha : |a-x| ≤ E*epsilon := _p2mH313 bits selection tagged sourcePrimary sourceBody source hprecision hbudget
  have hb : |b-y| ≤ (4*groupCount selection tagged:ℝ)*epsilon := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using _p2mH351 bits selection tagged source
  have hc : |c-z| ≤ (4*tagged.card:ℝ)*epsilon := by
    simpa only [c, z, word, epsilon, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, one_div, one_mul] using
      _p2mH333 bits selection tagged layout hroom source
  have hbb : |b| ≤ 1 := by rw [abs_of_nonneg (_p2mH350 bits selection tagged source).1]; exact (_p2mH350 bits selection tagged source).2
  have hxb : |x| ≤ 1 := _p2mH312 selection tagged sourcePrimary sourceBody source
  have hyb : |y| ≤ 1 := by rw [abs_of_nonneg (_p2mH348 selection tagged source).1]; exact (_p2mH348 selection tagged source).2
  have hzb : |z| ≤ 1 := _p2mH356 selection tagged layout source
  have hcb : |c| ≤ 1+4*tagged.card := by
    calc
      _ ≤ |c-z|+|z| := by simpa only [sub_add_cancel] using abs_add_le (c-z) z
      _ ≤ (4*tagged.card:ℝ)*epsilon+1 := add_le_add hc hzb
      _ ≤ _ := by nlinarith
  have hab := _p2mH346 a b x y 1 1 (E*epsilon) ((4*groupCount selection tagged:ℝ)*epsilon)
    (by norm_num) (by norm_num) (mul_nonneg (_p2mH326 security r s) he) (by positivity)
    hxb hbb ha hb
  have hxy : |x*y| ≤ 1 := by rw [abs_mul]; exact (mul_le_mul hxb hyb (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hall := _p2mH346 (a*b) c (x*y) z 1 (1+4*tagged.card)
    (E*epsilon*1+1*((4*groupCount selection tagged:ℝ)*epsilon)) ((4*tagged.card:ℝ)*epsilon)
    (by norm_num) (by positivity) (by positivity) (by positivity) hxy hcb hab hc
  unfold sourceScalar
  push_cast
  change |a*b*c-x*y*z| ≤ _
  exact hall.trans_eq (by unfold scalarError; dsimp only [E, epsilon]; ring)
open _root_.P2M9e1cfc64 renaming h332 → _p2mH332
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h340 {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (hroom : tagged.card ≤ Parameters.bodySize security)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(sourceScalar bits selection tagged sourcePrimary sourceBody source : ℝ)| ≤ scalarBound security r s tagged.card := by
  let word := sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
  have he := _p2mH168 bits
  have hE := _p2mH326 security r s
  have ha := _p2mH313 bits selection tagged sourcePrimary sourceBody source hprecision hbudget
  have hx := _p2mH312 selection tagged sourcePrimary sourceBody source
  have hb := _p2mH350 bits selection tagged source
  have hc := _p2mH333 bits selection tagged layout hroom source
  have hz := _p2mH356 selection tagged layout source
  have hcontrol : |(control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
      (fun index => (sourceBody index).val.val) word : ℝ)| ≤ 1+WeightedPointKernelProgram.errorConstant security r s := by
    calc
      _ ≤ |(control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
        (fun index => (sourceBody index).val.val) word : ℝ) -
        PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
          (fun group => (source group).2)| +
        |PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
          (fun group => (source group).2)| := by
        simpa only [sub_add_cancel] using abs_add_le
          ((control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
            (fun index => (sourceBody index).val.val) word : ℝ) -
            PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
              (fun group => (source group).2))
          (PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
              (fun group => (source group).2))
      _ ≤ WeightedPointKernelProgram.errorConstant security r s * (1/(2:ℝ)^bits)+1 := add_le_add ha hx
      _ ≤ _ := by nlinarith
  have hsigned : |(signed security bits (actualMetadata selection tagged) word : ℝ)| ≤ 1+4*tagged.card := by
    have hc' : |(signed security bits (actualMetadata selection tagged) word : ℝ)-
        RootWeightedSynthesis.weightedCoefficient selection tagged layout source| ≤
        (4*tagged.card:ℝ)*(1/(2:ℝ)^bits) := by
      simpa only [word, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, one_div, one_mul] using hc
    calc
      _ ≤ |(signed security bits (actualMetadata selection tagged) word : ℝ)-
        RootWeightedSynthesis.weightedCoefficient selection tagged layout source|+
        |RootWeightedSynthesis.weightedCoefficient selection tagged layout source| := by
        simpa only [sub_add_cancel] using abs_add_le
          ((signed security bits (actualMetadata selection tagged) word : ℝ)-
            RootWeightedSynthesis.weightedCoefficient selection tagged layout source)
          (RootWeightedSynthesis.weightedCoefficient selection tagged layout source)
      _ ≤ (4*tagged.card:ℝ)*(1/(2:ℝ)^bits)+1 := add_le_add hc' hz
      _ ≤ _ := by nlinarith
  unfold sourceScalar
  push_cast
  rw [abs_mul, abs_mul, abs_of_nonneg hb.1]
  exact (mul_le_mul (mul_le_mul hcontrol hb.2 hb.1 (by positivity)) hsigned (abs_nonneg _) (by positivity)).trans_eq
    (by unfold scalarBound; ring)
open _root_.P2M9e1cfc64 renaming h340 → _p2mH340
end
open _root_.P2M9e1cfc64 renaming h326 → _p2mH326
open _root_.P2M9e1cfc64 renaming h330 → _p2mH330
open _root_.P2M9e1cfc64 renaming h331 → _p2mH331
open _root_.P2M9e1cfc64 renaming h332 → _p2mH332
open _root_.P2M9e1cfc64 renaming h340 → _p2mH340
open _root_.P2M9e1cfc64 renaming h346 → _p2mH346
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M9e1cfc64 renaming h326 → _p2mH326
open _root_.P2M9e1cfc64 renaming h330 → _p2mH330
open _root_.P2M9e1cfc64 renaming h331 → _p2mH331
open _root_.P2M9e1cfc64 renaming h332 → _p2mH332
open _root_.P2M9e1cfc64 renaming h340 → _p2mH340
open _root_.P2M9e1cfc64 renaming h346 → _p2mH346
end
open _root_.P2M9e1cfc64 renaming h340 → _p2mH340
open _root_.P2M9e1cfc64 renaming h332 → _p2mH332
open _root_.P2M9e1cfc64 renaming h330 → _p2mH330
open _root_.P2M9e1cfc64 renaming h326 → _p2mH326
open _root_.P2M9e1cfc64 renaming h346 → _p2mH346
open _root_.P2M9e1cfc64 renaming h331 → _p2mH331
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
theorem _root_.P2M9e1cfc64.h401 (security order : ℕ) (roots : RootTaggedSelected.RootPair security) (source : Palette security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.primaryAt security order roots source arity).val colors centers| ≤ primaryBound security order := by
  let numerator := LocalRaisingLinear.completeFamilyLinear security order
    (RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single source 1)))
  have h := _p2mH196 order (data security order numerator) (data security order (LocalRaisingBounds.positiveInverse security order))
    (LocalCoefficientPointBounds.numeratorBound security) (RationalNormalizedPrimaryProgram.inverseBound security order)
    (_p2mH106 security) (_p2mH280 security order)
    (_p2mH107 security order roots source) (_p2mH278 security order)
    arity colors centers
  rw [_p2mH149] at h
  exact h
open _root_.P2M9e1cfc64 renaming h401 → _p2mH401
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h395 (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(SelectedOrdinaryHybrid.independentChannel security order horder (Pi.single source 1) arity).val colors centers| ≤
      (Fintype.card (TruncatedArity order) : ℝ)^2 * RationalSingletonProgram.inverseBound security order := by
  have h := _p2mH196 order
    (data security order (RaisingChannels.bodyLeading security order horder (Pi.single source 1)))
    (data security order (OrdinaryRaising.positiveInverse security order horder))
    1 (RationalSingletonProgram.inverseBound security order) (by norm_num)
    (_p2mH301 security order).1
    (_p2mH288 security order horder source)
    (_p2mH291 security order horder) arity colors centers
  rw [_p2mH149] at h
  have hchannel : SelectedOrdinaryHybrid.independentChannel security order horder (Pi.single source 1) =
      familyProduct (primaryLaw security) (bodyReference security) order
        (RaisingChannels.bodyLeading security order horder (Pi.single source 1))
        (OrdinaryRaising.positiveInverse security order horder) := by rfl
  rw [hchannel]
  simpa only [data, one_mul] using h
open _root_.P2M9e1cfc64 renaming h395 → _p2mH395
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h399 (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.hybridAt security order horder root (Pi.single source 1) arity).val colors centers| ≤ ordinaryBound security order := by
  have hmean : |∑ other : Root security, (rootReference security).weight other *
      (RootReferenceColumns.ordinaryAt security order horder other (Pi.single source 1) arity).val colors centers| ≤
      RationalOrdinaryFamilyProgram.atRootBound security order := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ other : Root security, (rootReference security).weight other * RationalOrdinaryFamilyProgram.atRootBound security order := by
        apply Finset.sum_le_sum
        intro other _
        rw [abs_mul, abs_of_nonneg ((rootReference security).nonneg other)]
        exact mul_le_mul_of_nonneg_left
          (_p2mH287 security order horder source other arity colors centers)
          ((rootReference security).nonneg other)
      _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  simp only [RootReferenceColumns.hybridAt, Pi.sub_apply, Pi.add_apply, Submodule.coe_sub, Submodule.coe_add,
    Finset.sum_apply, Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact (abs_sub _ _).trans ((add_le_add
    ((abs_add_le _ _).trans (add_le_add (_p2mH395 security order horder source arity colors centers)
      (_p2mH287 security order horder source root arity colors centers))) hmean).trans_eq
      (by unfold ordinaryBound; ring))
open _root_.P2M9e1cfc64 renaming h399 → _p2mH399
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h396 (security order : ℕ) (horder : 1 ≤ order) (root : Root security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.legAt security order horder root arity).val colors centers| ≤ legBound security order := by
  have h := _p2mH196 order (data security order (RationalUnselectedLegProgram.numeratorActual security order horder root))
    (data security order (RootLegReciprocal.reciprocal security order))
    (RationalUnselectedLegProgram.numeratorBound security) (RationalUnselectedLegProgram.inverseBound security order)
    (_p2mH476 security).1 (_p2mH472 security order).1
    (_p2mH466 security order horder root)
    (_p2mH465 security order) arity colors centers
  rw [_p2mH149] at h
  exact h
open _root_.P2M9e1cfc64 renaming h396 → _p2mH396
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h402 (security order : ℕ) (horder : 1 ≤ order) (bodyRole : UniformBodyProfiles.BodyRole)
    (queue : ℤ) (root : Root security) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.singletonAt security order horder bodyRole queue root arity).val colors centers| ≤ singletonBound security order := by
  have h := _p2mH196 order (data security order (RootReferenceColumns.singletonFirstAt security order horder bodyRole queue root))
    (data security order (RootMeanPrimary.positiveInverse security order horder bodyRole queue))
    (RationalSingletonProgram.firstBound security) (RationalSingletonProgram.inverseBound security order)
    (_p2mH443 security) (_p2mH301 security order).1
    (_p2mH438 security order horder bodyRole queue root)
    (_p2mH439 security order horder bodyRole queue) arity colors centers
  rw [_p2mH149] at h
  exact h
open _root_.P2M9e1cfc64 renaming h402 → _p2mH402
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h400 (security order : ℕ) : 1 ≤ pointBound security order := by
  unfold pointBound
  linarith [abs_nonneg (primaryBound security order), abs_nonneg (ordinaryBound security order),
    abs_nonneg (legBound security order), abs_nonneg (singletonBound security order)]
open _root_.P2M9e1cfc64 renaming h400 → _p2mH400
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h397 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : TaggedSelection.Selection security r s) (tagged : Finset (ActualBlockFock.BlockIndex security))
    (group : PairedRootPlacement.ActiveGroup selection tagged) (source : ActualRootGroupedChannel.Input selection tagged group)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.reducedColumn order horder queue selection tagged group source arity).val colors centers| ≤ pointBound security order := by
  have hp : primaryBound security order ≤ pointBound security order := by
    unfold pointBound
    linarith [le_abs_self (primaryBound security order), abs_nonneg (ordinaryBound security order),
      abs_nonneg (legBound security order), abs_nonneg (singletonBound security order)]
  have ho : ordinaryBound security order ≤ pointBound security order := by
    unfold pointBound
    linarith [le_abs_self (ordinaryBound security order), abs_nonneg (primaryBound security order),
      abs_nonneg (legBound security order), abs_nonneg (singletonBound security order)]
  have hl : legBound security order ≤ pointBound security order := by
    unfold pointBound
    linarith [le_abs_self (legBound security order), abs_nonneg (ordinaryBound security order),
      abs_nonneg (primaryBound security order), abs_nonneg (singletonBound security order)]
  have hs : singletonBound security order ≤ pointBound security order := by
    unfold pointBound
    linarith [le_abs_self (singletonBound security order), abs_nonneg (ordinaryBound security order),
      abs_nonneg (legBound security order), abs_nonneg (primaryBound security order)]
  rcases group with (primary | ordinary) | kept
  · exact (_p2mH401 security order _ source.2 arity colors centers).trans hp
  · exact (_p2mH399 security order horder source.2 (source.1 (0 : Fin 1)) arity colors centers).trans ho
  · rcases hk : kept.val.val with leg | (center | point)
    · simpa only [RootReferenceColumns.reducedColumn, RootReferenceColumns.unselectedAt, hk] using
        (_p2mH396 security order horder (source.1 (0 : Fin 1)) arity colors centers).trans hl
    · have hfree : RootReferenceColumns.singletonAt security order horder .free queue (source.1 (0 : Fin 1)) =
          RootReferenceColumns.singletonAt security order horder .free 0 (source.1 (0 : Fin 1)) := by rfl
      simpa only [RootReferenceColumns.reducedColumn, RootReferenceColumns.unselectedAt, hk, hfree] using
        (_p2mH402 security order horder .free queue (source.1 (0 : Fin 1)) arity colors centers).trans hs
    · simpa only [RootReferenceColumns.reducedColumn, RootReferenceColumns.unselectedAt, hk] using
        (_p2mH402 security order horder .queue queue (source.1 (0 : Fin 1)) arity colors centers).trans hs
open _root_.P2M9e1cfc64 renaming h397 → _p2mH397
end
open _root_.P2M9e1cfc64 renaming h395 → _p2mH395
open _root_.P2M9e1cfc64 renaming h396 → _p2mH396
open _root_.P2M9e1cfc64 renaming h397 → _p2mH397
open _root_.P2M9e1cfc64 renaming h399 → _p2mH399
open _root_.P2M9e1cfc64 renaming h400 → _p2mH400
open _root_.P2M9e1cfc64 renaming h401 → _p2mH401
open _root_.P2M9e1cfc64 renaming h402 → _p2mH402
end CurrentAFT.RationalRootGroupProgram
open _root_.P2M9e1cfc64 renaming h395 → _p2mH395
open _root_.P2M9e1cfc64 renaming h396 → _p2mH396
open _root_.P2M9e1cfc64 renaming h397 → _p2mH397
open _root_.P2M9e1cfc64 renaming h399 → _p2mH399
open _root_.P2M9e1cfc64 renaming h400 → _p2mH400
open _root_.P2M9e1cfc64 renaming h401 → _p2mH401
open _root_.P2M9e1cfc64 renaming h402 → _p2mH402
end
open _root_.P2M9e1cfc64 renaming h402 → _p2mH402
open _root_.P2M9e1cfc64 renaming h400 → _p2mH400
open _root_.P2M9e1cfc64 renaming h401 → _p2mH401
open _root_.P2M9e1cfc64 renaming h397 → _p2mH397
open _root_.P2M9e1cfc64 renaming h395 → _p2mH395
open _root_.P2M9e1cfc64 renaming h399 → _p2mH399
open _root_.P2M9e1cfc64 renaming h396 → _p2mH396
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
theorem _root_.P2M9e1cfc64.h320 {security r s : ℕ} (bits order : ℕ) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged) :
    interpret security order (localProduct security bits order queue (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source))) =
      RationalFamilyWordProduct.current order (groupCount selection tagged) (fun index =>
        interpret security order (RationalRootGroupProgram.table bits order queue selection tagged
          (ordering selection tagged index) (source (ordering selection tagged index)))) := by
  have ht : (fun index => localTable security bits order queue ((actualMetadata selection tagged).roles index)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source) index)) =
      fun index => RationalRootGroupProgram.table bits order queue selection tagged
        (ordering selection tagged index) (source (ordering selection tagged index)) := by
    funext index
    rw [_p2mH342]
    rfl
  unfold localProduct
  rw [ht, _p2mH214]
  rfl
open _root_.P2M9e1cfc64 renaming h320 → _p2mH320
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h323 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged) :
    RationalFamilyWordProduct.current order (groupCount selection tagged) (fun index => data security order
      (RootReferenceColumns.reducedColumn order horder queue selection tagged
        (ordering selection tagged index) (source (ordering selection tagged index)))) =
      data security order (productActual order horder queue selection tagged source) := by
  unfold data
  rw [_p2mH211]
  have hp := (ordering selection tagged).prod_comp (fun group =>
    RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group))
  exact congrArg (fun family : BackgroundFamilies.ActualFamily security order =>
    fun arity => (family arity).val) hp
open _root_.P2M9e1cfc64 renaming h323 → _p2mH323
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h318 (security order : ℕ) : 1 ≤ localGrowth security order :=
  _p2mH184 _ _ _ ((by norm_num : (0 : ℝ) ≤ 1).trans (_p2mH400 security order))
    (_p2mH394 security order)
open _root_.P2M9e1cfc64 renaming h318 → _p2mH318
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h319 {security r s : ℕ} (bits order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (localProduct security bits order queue (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source))) arity colors centers -
      data security order (productActual order horder queue selection tagged source) arity colors centers| ≤
      localProductError security order (groupCount selection tagged) * (1 / (2 : ℝ)^bits) := by
  let A := RationalRootGroupProgram.pointBound security order
  let E := RationalRootGroupProgram.errorConstant security order
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  have hA : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (_p2mH400 security order)
  have hE : 0 ≤ E := _p2mH394 security order
  have he : 0 ≤ epsilon := by positivity
  have hsmall : E * epsilon ≤ E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (_p2mH168 bits) hE
  have hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * (A + E*epsilon + 1) ≤ localGrowth security order := by
    apply le_trans _ (_p2mH185 order A E)
    gcongr
  have h := _p2mH213 order (groupCount selection tagged)
    (fun index => data security order (RootReferenceColumns.reducedColumn order horder queue selection tagged
      (ordering selection tagged index) (source (ordering selection tagged index))))
    (fun index => interpret security order (RationalRootGroupProgram.table bits order queue selection tagged
      (ordering selection tagged index) (source (ordering selection tagged index))))
    A (E*epsilon) (localGrowth security order) hA (by positivity) (_p2mH318 security order) hscale
    (fun index => _p2mH397 order horder queue selection tagged _ _)
    (fun index => _p2mH398 bits order horder queue selection tagged _ _ hfirst hprecision hbudget)
    arity colors centers
  rw [← _p2mH320, _p2mH323] at h
  exact h.trans_eq (by unfold localProductError; dsimp only [E, epsilon]; ring)
open _root_.P2M9e1cfc64 renaming h319 → _p2mH319
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h327 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |data security order (productActual order horder queue selection tagged source) arity colors centers| ≤
      (localGrowth security order)^(groupCount selection tagged) := by
  let A := RationalRootGroupProgram.pointBound security order
  have hA : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (_p2mH400 security order)
  have hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * A ≤ localGrowth security order := by
    apply le_trans _ (_p2mH185 order A (RationalRootGroupProgram.errorConstant security order))
    gcongr
    have hE := _p2mH394 security order
    linarith
  have h := _p2mH212 order (groupCount selection tagged)
    (fun index => data security order (RootReferenceColumns.reducedColumn order horder queue selection tagged
      (ordering selection tagged index) (source (ordering selection tagged index)))) A (localGrowth security order)
    hA (_p2mH318 security order) hscale
    (fun index => _p2mH397 order horder queue selection tagged _ _) arity colors centers
  rw [_p2mH323] at h
  exact h
open _root_.P2M9e1cfc64 renaming h327 → _p2mH327
end
open _root_.P2M9e1cfc64 renaming h318 → _p2mH318
open _root_.P2M9e1cfc64 renaming h319 → _p2mH319
open _root_.P2M9e1cfc64 renaming h320 → _p2mH320
open _root_.P2M9e1cfc64 renaming h323 → _p2mH323
open _root_.P2M9e1cfc64 renaming h327 → _p2mH327
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M9e1cfc64 renaming h318 → _p2mH318
open _root_.P2M9e1cfc64 renaming h319 → _p2mH319
open _root_.P2M9e1cfc64 renaming h320 → _p2mH320
open _root_.P2M9e1cfc64 renaming h323 → _p2mH323
open _root_.P2M9e1cfc64 renaming h327 → _p2mH327
end
open _root_.P2M9e1cfc64 renaming h327 → _p2mH327
open _root_.P2M9e1cfc64 renaming h323 → _p2mH323
open _root_.P2M9e1cfc64 renaming h318 → _p2mH318
open _root_.P2M9e1cfc64 renaming h320 → _p2mH320
open _root_.P2M9e1cfc64 renaming h319 → _p2mH319
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
theorem _root_.P2M9e1cfc64.h337 (security order r s count tags : ℕ) :
    0 ≤ sourceError security order r s count tags := by
  unfold sourceError
  have hs := _p2mH330 security r s tags
  have he := _p2mH331 security r s count tags
  have hE := _p2mH394 security order
  have hC := (by norm_num : (0:ℝ)≤1).trans (_p2mH318 security order)
  positivity
open _root_.P2M9e1cfc64 renaming h337 → _p2mH337
set_option maxRecDepth 8192
theorem _root_.P2M9e1cfc64.h344 {security r s : ℕ} (bits order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ Vertex security) (hroom : tagged.card ≤ Parameters.bodySize security)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (summand security bits order queue (actualMetadata selection tagged)
        (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)
        (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source))) arity colors centers -
      actualScalar selection tagged layout sourcePrimary sourceBody source *
        data security order (productActual order horder queue selection tagged source) arity colors centers| ≤
      sourceError security order r s (groupCount selection tagged) tagged.card*(1/(2:ℝ)^bits) := by
  let word := sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
  have hvalue : interpret security order (summand security bits order queue (actualMetadata selection tagged)
      (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val) word) arity colors centers =
      interpret security order (localProduct security bits order queue (actualMetadata selection tagged) word) arity colors centers *
        (sourceScalar bits selection tagged sourcePrimary sourceBody source:ℝ) := by
    unfold interpret RationalFamilyProductProgram.pullback RationalFamilyProductProgram.realTable summand
    rw [if_pos (_p2mH355 selection tagged source)]
    push_cast
    unfold sourceScalar
    push_cast
    ring
  rw [hvalue, mul_comm (actualScalar _ _ _ _ _ _)]
  have hC := (by norm_num : (0:ℝ)≤1).trans (_p2mH318 security order)
  have h := _p2mH346
    (interpret security order (localProduct security bits order queue (actualMetadata selection tagged) word) arity colors centers)
    (sourceScalar bits selection tagged sourcePrimary sourceBody source:ℝ)
    (data security order (productActual order horder queue selection tagged source) arity colors centers)
    (actualScalar selection tagged layout sourcePrimary sourceBody source)
    ((localGrowth security order)^(groupCount selection tagged)) (scalarBound security r s tagged.card)
    (localProductError security order (groupCount selection tagged)*(1/(2:ℝ)^bits))
    (scalarError security r s (groupCount selection tagged) tagged.card*(1/(2:ℝ)^bits))
    (by positivity) (_p2mH330 security r s tagged.card) (by
      unfold localProductError
      have he := _p2mH394 security order
      have hc := (by norm_num : (0:ℝ)≤1).trans (_p2mH318 security order)
      positivity) (mul_nonneg (_p2mH331 _ _ _ _ _) (by positivity))
    (_p2mH327 order horder queue selection tagged source arity colors centers)
    (_p2mH340 bits selection tagged layout hroom sourcePrimary sourceBody source hprecision hbudget)
    (_p2mH319 bits order horder queue selection tagged source hfirst hprecision hbudget arity colors centers)
    (_p2mH332 bits selection tagged layout hroom sourcePrimary sourceBody source hprecision hbudget)
  exact h.trans_eq (by unfold sourceError localProductError; ring)
open _root_.P2M9e1cfc64 renaming h344 → _p2mH344
set_option maxRecDepth 8192
theorem _root_.CurrentAFT.RationalPackedRootProgram.__p2m_proof_9e1cfc6401f068b0d10d {security r s : ℕ} (bits order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ Vertex security) (hroom : tagged.card ≤ Parameters.bodySize security)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (current security bits order queue (actualMetadata selection tagged)
        (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)) arity colors centers -
      data security order (ActualRootResponse.response order horder queue selection tagged layout
        (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)) arity colors centers| ≤
      rawErrorConstant security order r s (groupCount selection tagged) tagged.card*(1/(2:ℝ)^bits) := by
  have hresponse : data security order (ActualRootResponse.response order horder queue selection tagged layout
      (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)) arity colors centers =
      ∑ index : Fin ((CurrentRectangleIndex.colors security)^((groupCount selection tagged)*3)),
        (CurrentGroupSourcePadding.decode selection tagged (CurrentRootOrdering.keptOrdering selection tagged) index).elim 0
          (fun source => actualScalar selection tagged layout sourcePrimary sourceBody source *
            data security order (productActual order horder queue selection tagged source) arity colors centers) := by
    rw [_p2mH60 order horder queue selection tagged (CurrentRootOrdering.keptOrdering selection tagged)]
    simp only [data, Finset.sum_apply, Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro index _
    cases CurrentGroupSourcePadding.decode selection tagged (CurrentRootOrdering.keptOrdering selection tagged) index with
    | none => rfl
    | some source =>
      simp only [Option.elim_some, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul]
      have hp : (∏ group, RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group)) =
          productActual order horder queue selection tagged source := by
        unfold productActual
        apply Finset.prod_congr (by ext; simp)
        intro group _
        rfl
      rw [hp]
      rfl
  have hcomputed : interpret security order (current security bits order queue (actualMetadata selection tagged)
      (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)) arity colors centers =
      ∑ index : Fin ((CurrentRectangleIndex.colors security)^((groupCount selection tagged)*3)),
        interpret security order (summand security bits order queue (actualMetadata selection tagged)
          (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)
          (sourceWord security (groupCount selection tagged) index)) arity colors centers := by
    simp only [interpret, RationalFamilyProductProgram.pullback, RationalFamilyProductProgram.realTable, current, Rat.cast_sum]
    rfl
  rw [hcomputed, hresponse, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _index : Fin ((CurrentRectangleIndex.colors security)^((groupCount selection tagged)*3)),
        sourceError security order r s (groupCount selection tagged) tagged.card*(1/(2:ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro index _
      cases hd : CurrentGroupSourcePadding.decode selection tagged (CurrentRootOrdering.keptOrdering selection tagged) index with
      | none =>
        have hv := (_p2mH316 selection tagged index).mp hd
        simp only [Option.elim_none, interpret, RationalFamilyProductProgram.pullback,
          RationalFamilyProductProgram.realTable, summand, hv, ite_false, Rat.cast_zero, sub_zero, abs_zero]
        exact mul_nonneg (_p2mH337 _ _ _ _ _ _) (by positivity)
      | some source =>
        have hi := (_p2mH315 selection tagged index source).mp hd
        subst index
        exact _p2mH344 bits order horder queue selection tagged layout hroom sourcePrimary sourceBody source
          hfirst hprecision hbudget arity colors centers
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, rawErrorConstant]; ring
end
open _root_.P2M9e1cfc64 renaming h337 → _p2mH337
open _root_.P2M9e1cfc64 renaming h344 → _p2mH344
end CurrentAFT.RationalPackedRootProgram
open _root_.P2M9e1cfc64 renaming h337 → _p2mH337
open _root_.P2M9e1cfc64 renaming h344 → _p2mH344
end
open _root_.P2M9e1cfc64 renaming h337 → _p2mH337
open _root_.P2M9e1cfc64 renaming h344 → _p2mH344
set_option maxRecDepth 65536
theorem solution : (type_of% @_root_.CurrentAFT.RationalPackedRootProgram.__p2m_proof_9e1cfc6401f068b0d10d) := @_root_.CurrentAFT.RationalPackedRootProgram.__p2m_proof_9e1cfc6401f068b0d10d
