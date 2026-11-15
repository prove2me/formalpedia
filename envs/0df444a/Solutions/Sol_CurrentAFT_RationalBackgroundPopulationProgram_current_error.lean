-- Prove2me | solution 1 for CurrentAFT.RationalBackgroundPopulationProgram.current_error
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T18:48:11.315426+00:00
-- url     : https://prove2.me/submissions/f390b273-018d-4bdf-b956-2b473dbb1c02

import Definitions.Def_InfoLossLAR_NativeBundle_09
import Theorems.Thm_AFT_FiniteDist_l1_prod_le
namespace P2M7374ab17
end P2M7374ab17
section
namespace AFT.RationalNumerics
open scoped BigOperators
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h1 (value : ℝ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (index : ℕ) :
    |(-1 : ℝ)^index*value^(2*index+1)/(2*index+1 : ℕ)| ≤ (1/2 : ℝ)^(index+1) := by
  rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (pow_nonneg hv _),abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ value^(2*index+1) := div_le_self (pow_nonneg hv _) (by exact_mod_cast (show 1≤2*index+1 by omega))
    _ ≤ (1/2 : ℝ)^(2*index+1) := pow_le_pow_left₀ hv hv' _
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
open _root_.P2M7374ab17 renaming h1 → _p2mH1
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h0 (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (terms : ℕ) :
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
    have hh := _p2mH1 (value : ℝ) hv0 hv1 (i+terms)
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
open _root_.P2M7374ab17 renaming h0 → _p2mH0
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h11 (bits : ℕ) : |(piApprox bits : ℝ)-Real.pi| ≤ 1/(2 : ℝ)^bits := by
  have h1 := _p2mH0 (1/2) (by norm_num) (by norm_num) (bits+3)
  have h2 := _p2mH0 (1/3) (by norm_num) (by norm_num) (bits+3)
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
open _root_.P2M7374ab17 renaming h11 → _p2mH11
end
open _root_.P2M7374ab17 renaming h0 → _p2mH0
open _root_.P2M7374ab17 renaming h1 → _p2mH1
open _root_.P2M7374ab17 renaming h11 → _p2mH11
end AFT.RationalNumerics
open _root_.P2M7374ab17 renaming h0 → _p2mH0
open _root_.P2M7374ab17 renaming h1 → _p2mH1
open _root_.P2M7374ab17 renaming h11 → _p2mH11
end
open _root_.P2M7374ab17 renaming h1 → _p2mH1
open _root_.P2M7374ab17 renaming h11 → _p2mH11
open _root_.P2M7374ab17 renaming h0 → _p2mH0
section
namespace AFT.RationalNumerics
open scoped BigOperators
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h6 (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2)
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
open _root_.P2M7374ab17 renaming h6 → _p2mH6
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h10 (first second : ℝ) (hf : 1 ≤ first) (hs : 1 ≤ second) :
    |first⁻¹-second⁻¹| ≤ |first-second| := by
  have hfirst : first ≠ 0 := by linarith
  have hsecond : second ≠ 0 := by linarith
  have he : first⁻¹-second⁻¹=(second-first)/(first*second) := by field_simp
  rw [he,abs_div,abs_sub_comm,abs_of_nonneg (by positivity : 0 ≤ first*second)]
  exact div_le_self (abs_nonneg _) (by nlinarith)
open _root_.P2M7374ab17 renaming h10 → _p2mH10
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h12 (first second : ℝ)
    (hf : 0 ≤ first ∧ first ≤ 1) (hs : 0 ≤ second ∧ second ≤ 1) (count : ℕ) :
    |first^count-second^count| ≤ (count : ℝ)*|first-second| := by
  have hh := abs_pow_sub_pow_le first second count
  rw [abs_of_nonneg hf.1,abs_of_nonneg hs.1] at hh
  have hp : max first second^(count-1) ≤ 1 := pow_le_one₀ (le_max_of_le_left hf.1) (max_le hf.2 hs.2)
  calc
    _ ≤ |first-second| *count*max first second^(count-1) := hh
    _ ≤ |first-second| *count*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring
open _root_.P2M7374ab17 renaming h12 → _p2mH12
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h5 (argument : ℚ) (scale bits : ℕ)
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
  have hpi := _p2mH12 ((expSum value terms : ℝ)⁻¹) ((Real.exp (value : ℝ))⁻¹)
    ⟨by positivity,inv_le_one_of_one_le₀ hfirst⟩ ⟨by positivity,inv_le_one_of_one_le₀ hsecond⟩ scale
  have hi := _p2mH10 (expSum value terms) (Real.exp (value : ℝ)) hfirst hsecond
  have happrox := (hpi.trans (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg scale))).trans
    (mul_le_mul_of_nonneg_left (_p2mH6 value hv0 hv1 terms ht) (Nat.cast_nonneg scale))
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
open _root_.P2M7374ab17 renaming h5 → _p2mH5
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h4 (argument : ℚ) (bits : ℕ) :
    |(expNegApprox argument bits : ℝ)-Real.exp (-max (argument : ℝ) 0)| ≤ 1/(2 : ℝ)^bits := by
  have hb : 2*max argument 0 ≤ (expScale argument : ℚ) := by
    have hh := Nat.le_ceil (max argument 0)
    simp only [expScale,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    linarith
  have hh := _p2mH5 (max argument 0) (expScale argument) bits
    (le_max_right _ _) (expScale_positive argument) hb
  simpa only [expNegApprox,Rat.cast_max,Rat.cast_zero] using hh
open _root_.P2M7374ab17 renaming h4 → _p2mH4
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h7 (first second : ℝ) (hf : 0 ≤ first) (hs : 0 ≤ second) :
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
open _root_.P2M7374ab17 renaming h7 → _p2mH7
end
open _root_.P2M7374ab17 renaming h4 → _p2mH4
open _root_.P2M7374ab17 renaming h5 → _p2mH5
open _root_.P2M7374ab17 renaming h6 → _p2mH6
open _root_.P2M7374ab17 renaming h7 → _p2mH7
open _root_.P2M7374ab17 renaming h10 → _p2mH10
open _root_.P2M7374ab17 renaming h12 → _p2mH12
end AFT.RationalNumerics
open _root_.P2M7374ab17 renaming h4 → _p2mH4
open _root_.P2M7374ab17 renaming h5 → _p2mH5
open _root_.P2M7374ab17 renaming h6 → _p2mH6
open _root_.P2M7374ab17 renaming h7 → _p2mH7
open _root_.P2M7374ab17 renaming h10 → _p2mH10
open _root_.P2M7374ab17 renaming h12 → _p2mH12
end
open _root_.P2M7374ab17 renaming h7 → _p2mH7
open _root_.P2M7374ab17 renaming h4 → _p2mH4
open _root_.P2M7374ab17 renaming h6 → _p2mH6
open _root_.P2M7374ab17 renaming h10 → _p2mH10
open _root_.P2M7374ab17 renaming h5 → _p2mH5
open _root_.P2M7374ab17 renaming h12 → _p2mH12
section
namespace AFT.RationalNumerics
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h8 (squaredWidth : ℚ) (point : ℤ) (bits : ℕ)
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
  have hpi := _p2mH11 (bits+guard+1)
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
  have he := _p2mH4 argument (bits+1)
  have hl := _p2mH7 (max (argument : ℝ) 0) (Real.pi*(ratio : ℝ)) (le_max_right _ _) ht
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
open _root_.P2M7374ab17 renaming h8 → _p2mH8
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h9 (squaredWidth : ℚ) (width : ℝ) (point : ℤ) (bits : ℕ)
    (hwidth : 0 < squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) :
    |(gaussianApprox squaredWidth point bits : ℝ)-GaussianSource.weight width point| ≤ 1/(2 : ℝ)^bits := by
  convert _p2mH8 squaredWidth point bits hwidth using 1
  unfold GaussianSource.weight
  rw [hsquare]
  have h : -(Real.pi / (squaredWidth : ℝ)) * (point : ℝ)^2 =
      -Real.pi * (point : ℝ)^2 / (squaredWidth : ℝ) := by ring
  rw [h]
open _root_.P2M7374ab17 renaming h9 → _p2mH9
end
open _root_.P2M7374ab17 renaming h8 → _p2mH8
open _root_.P2M7374ab17 renaming h9 → _p2mH9
end AFT.RationalNumerics
open _root_.P2M7374ab17 renaming h8 → _p2mH8
open _root_.P2M7374ab17 renaming h9 → _p2mH9
end
open _root_.P2M7374ab17 renaming h8 → _p2mH8
open _root_.P2M7374ab17 renaming h9 → _p2mH9
section
namespace AFT.SignedConditioning
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h17 (first second : Color → ℝ) :
    |(∑ color, first color) - ∑ color, second color| ≤ ∑ color, |first color - second color| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _
open _root_.P2M7374ab17 renaming h17 → _p2mH17
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h18 (signed reference : Color → ℝ)
    (href : ∀ color, 0 ≤ reference color)
    (hsigned : 0 < ∑ color, signed color) (hreference : 0 < ∑ color, reference color) :
    (∑ color, |signed color / (∑ x, signed x) - reference color / (∑ x, reference x)|) ≤
      2 * (∑ color, |signed color - reference color|) / (∑ color, signed color) := by
  let total := ∑ color, signed color
  let referenceTotal := ∑ color, reference color
  let error := ∑ color, |signed color - reference color|
  have hmass : |referenceTotal - total| ≤ error := by
    simpa only [abs_sub_comm] using _p2mH17 signed reference
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
open _root_.P2M7374ab17 renaming h18 → _p2mH18
end
open _root_.P2M7374ab17 renaming h17 → _p2mH17
open _root_.P2M7374ab17 renaming h18 → _p2mH18
end AFT.SignedConditioning
open _root_.P2M7374ab17 renaming h17 → _p2mH17
open _root_.P2M7374ab17 renaming h18 → _p2mH18
end
open _root_.P2M7374ab17 renaming h17 → _p2mH17
open _root_.P2M7374ab17 renaming h18 → _p2mH18
section
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h16 (squaredWidth : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hwidth : 0 < squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) :
    (∑ point,|(windowApproxLaw squaredWidth cutoff bits).weight point-
      (windowGaussian width cutoff).weight point|) ≤ 1/(2 : ℝ)^bits := by
  let raw : Window cutoff → ℝ := fun point => (windowApproxRaw squaredWidth cutoff bits point : ℝ)
  have hraw : 1 ≤ ∑ point,raw point := by
    have hh := windowApproxNormalizer_ge_one squaredWidth cutoff bits
    rw [windowApproxNormalizer_eq_sum] at hh
    dsimp only [raw]
    exact_mod_cast hh
  have hnormal := _p2mH18 raw (fun point => GaussianSource.weight width point)
    (fun point => (weight_pos _ _).le) (zero_lt_one.trans_le hraw)
    (zero_lt_one.trans_le (windowNormalizer_ge_one width cutoff))
  have herr : (∑ point,|raw point-GaussianSource.weight width point|) ≤
      (2*cutoff+1 : ℕ)/(2 : ℝ)^(windowApproxPrecision cutoff bits) := by
    have hh := Finset.sum_le_sum (fun point (_ : point ∈ (Finset.univ : Finset (Window cutoff))) =>
      _p2mH9 squaredWidth width point (windowApproxPrecision cutoff bits) hwidth hsquare)
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
open _root_.P2M7374ab17 renaming h16 → _p2mH16
end
open _root_.P2M7374ab17 renaming h16 → _p2mH16
end AFT.RationalNumerics
open _root_.P2M7374ab17 renaming h16 → _p2mH16
end
open _root_.P2M7374ab17 renaming h16 → _p2mH16
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
theorem _root_.P2M7374ab17.h29 (ρ scalar : ℝ) (hsmall : |scalar| ≤ ρ / 2) :
    ρ / 2 ≤ ρ + scalar := by
  have := (abs_le.mp hsmall).1
  linarith
open _root_.P2M7374ab17 renaming h29 → _p2mH29
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
open _root_.P2M7374ab17 renaming h29 → _p2mH29
end
open _root_.P2M7374ab17 renaming h29 → _p2mH29
section
namespace AFT
open scoped BigOperators
section FiniteProfiles
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
end FiniteProfiles
section SignProfile
variable {ι : Type*} [Fintype ι]
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h28 (activation : ℝ) (signProfile sign : ι → ℝ)
    (hsign : ∀ color, |sign color| ≤ 1)
    (hsmall : (∑ color, |signProfile color|) < activation) (profile : ι → ℝ) :
    (finitePrimaryRankEquiv activation signProfile sign hsign hsmall).symm profile =
      profile - ((activation + signFunctional sign signProfile)⁻¹ *
        signFunctional sign profile) • signProfile := by
  exact primaryRankInverse_apply activation signProfile (profileSignMap sign) profile
open _root_.P2M7374ab17 renaming h28 → _p2mH28
end SignProfile
open _root_.P2M7374ab17 renaming h28 → _p2mH28
end AFT
open _root_.P2M7374ab17 renaming h28 → _p2mH28
end
open _root_.P2M7374ab17 renaming h28 → _p2mH28
section
namespace AFT
open scoped BigOperators
namespace TrimmedSlice
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h21 (modulus boundary shift color : ℤ) :
    law modulus boundary shift (modulus - 1 - color) = law modulus boundary (-shift) color := by
  have hm : modulus - 1 - color ∈ slice modulus boundary shift ↔ color ∈ slice modulus boundary (-shift) := by
    simp only [mem_slice]
    omega
  simp only [law, hm, slice_card, abs_neg]
open _root_.P2M7374ab17 renaming h21 → _p2mH21
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h20 (start color : ℤ) (width : ℕ) :
    intervalAnchorLaw (reflectedStart start width) width (-color) = intervalAnchorLaw start width color := by
  have hm : -color ∈ anchorInterval (reflectedStart start width) width ↔ color ∈ anchorInterval start width := by
    simp only [anchorInterval, Finset.mem_Ico, reflectedStart]
    omega
  simp only [intervalAnchorLaw, hm]
open _root_.P2M7374ab17 renaming h20 → _p2mH20
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h19 (modulus boundary start source color : ℤ) (width : ℕ) :
    averagedLaw modulus boundary start source width (modulus - 1 - color) =
      averagedLaw modulus boundary (reflectedStart start width) (-source) width color := by
  unfold averagedLaw intervalMixture
  apply Finset.sum_bij (fun offset _ => -offset)
  · intro offset ho
    simp only [anchorInterval, Finset.mem_Ico, reflectedStart] at ho ⊢
    omega
  · intro a _ b _ hab
    omega
  · intro offset ho
    refine ⟨-offset, ?_, by omega⟩
    simp only [anchorInterval, Finset.mem_Ico, reflectedStart] at ho ⊢
    omega
  · intro offset _
    dsimp only
    rw [_p2mH20, _p2mH21]
    congr 2
    ring
open _root_.P2M7374ab17 renaming h19 → _p2mH19
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h22 {τ : Type*} [Fintype τ]
    (modulus boundary : ℤ) (width : ℕ) (starts targets sources : τ → ℤ) (weights : τ → ℝ)
    (reverse : τ ≃ τ) (hw : ∀ index, weights (reverse index) = weights index)
    (hs : ∀ index, sources (reverse index) = -sources index)
    (ha : ∀ index, targets (reverse index) = reflectedStart (starts index) width) (color : ℤ) :
    mixedLaw modulus boundary starts sources weights width (modulus - 1 - color) =
      mixedLaw modulus boundary targets sources weights width color := by
  unfold mixedLaw
  calc
    _ = ∑ index, weights (reverse index) * averagedLaw modulus boundary
        (targets (reverse index)) (sources (reverse index)) width color := by
      apply Finset.sum_congr rfl
      intro index _
      rw [hw, ha, hs, _p2mH19]
    _ = _ := Equiv.sum_comp reverse (fun index => weights index *
      averagedLaw modulus boundary (targets index) (sources index) width color)
open _root_.P2M7374ab17 renaming h22 → _p2mH22
end TrimmedSlice
open _root_.P2M7374ab17 renaming h19 → _p2mH19
open _root_.P2M7374ab17 renaming h20 → _p2mH20
open _root_.P2M7374ab17 renaming h21 → _p2mH21
open _root_.P2M7374ab17 renaming h22 → _p2mH22
namespace V7Calibration
end V7Calibration
end AFT
open _root_.P2M7374ab17 renaming h19 → _p2mH19
open _root_.P2M7374ab17 renaming h20 → _p2mH20
open _root_.P2M7374ab17 renaming h21 → _p2mH21
open _root_.P2M7374ab17 renaming h22 → _p2mH22
end
open _root_.P2M7374ab17 renaming h22 → _p2mH22
open _root_.P2M7374ab17 renaming h19 → _p2mH19
open _root_.P2M7374ab17 renaming h21 → _p2mH21
open _root_.P2M7374ab17 renaming h20 → _p2mH20
section
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators
noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h26 (start : ℤ) (width : ℕ) (point : ℤ) :
    |(intervalProbabilityProgram start width point : ℝ)|≤1 := by
  rw [intervalProbabilityProgram_cast,abs_of_nonneg (intervalAnchorLaw_nonneg _ _ _)]
  apply (intervalAnchorLaw_bound _ _ _).trans
  by_cases hw : width=0
  · subst width; norm_num
  have hh : (1 : ℝ)≤width := by exact_mod_cast (show 1≤width by omega)
  exact inv_le_one_of_one_le₀ hh
open _root_.P2M7374ab17 renaming h26 → _p2mH26
end
open _root_.P2M7374ab17 renaming h26 → _p2mH26
end AFT.V7Calibration
open _root_.P2M7374ab17 renaming h26 → _p2mH26
end
open _root_.P2M7374ab17 renaming h26 → _p2mH26
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
theorem _root_.P2M7374ab17.h27 (modulus boundary shift color : ℤ) :
    |(sliceProbabilityProgram modulus boundary shift color : ℝ)|≤1 := by
  rw [sliceProbabilityProgram_eq_original]
  split_ifs with hh
  · simp only [Rat.cast_inv,Rat.cast_natCast]
    rw [abs_of_nonneg (by positivity)]
    apply inv_le_one_of_one_le₀
    exact_mod_cast (Finset.one_le_card.mpr ⟨color,hh⟩)
  · norm_num
open _root_.P2M7374ab17 renaming h27 → _p2mH27
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h25 (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
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
        (_p2mH27 modulus boundary (shift-source) color)
        (intervalAnchorLaw_nonneg start shift width)
    _ = 1 := intervalAnchorLaw_mass start width hw
open _root_.P2M7374ab17 renaming h25 → _p2mH25
end
open _root_.P2M7374ab17 renaming h25 → _p2mH25
open _root_.P2M7374ab17 renaming h27 → _p2mH27
end AFT.V7Calibration
open _root_.P2M7374ab17 renaming h25 → _p2mH25
open _root_.P2M7374ab17 renaming h27 → _p2mH27
end
open _root_.P2M7374ab17 renaming h27 → _p2mH27
open _root_.P2M7374ab17 renaming h25 → _p2mH25
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
theorem _root_.P2M7374ab17.h24 (modulus : ℕ) (boundary start source : ℤ) (width : ℕ)
    (first second : Fin modulus) :
    (averagedPairProgram modulus boundary start source width first.val second.val : ℝ)=
      TrimmedSlice.averagedPair modulus boundary start source width first second := by
  simp only [averagedPairProgram,Rat.cast_mul,intervalProbabilityProgram_cast,sliceProbabilityProgram_cast,
    TrimmedSlice.averagedPair_formula]
open _root_.P2M7374ab17 renaming h24 → _p2mH24
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h23 (modulus : ℕ) (boundary start source : ℤ) (width first second : ℕ) :
    |(averagedPairProgram modulus boundary start source width first second : ℝ)| ≤ 1 := by
  simp only [averagedPairProgram,Rat.cast_mul,abs_mul]
  exact (mul_le_mul (_p2mH26 _ _ _) (_p2mH27 _ _ _ _)
    (abs_nonneg _) (by norm_num)).trans_eq (mul_one _)
open _root_.P2M7374ab17 renaming h23 → _p2mH23
end
open _root_.P2M7374ab17 renaming h23 → _p2mH23
open _root_.P2M7374ab17 renaming h24 → _p2mH24
end AFT.V7Calibration
open _root_.P2M7374ab17 renaming h23 → _p2mH23
open _root_.P2M7374ab17 renaming h24 → _p2mH24
end
open _root_.P2M7374ab17 renaming h23 → _p2mH23
open _root_.P2M7374ab17 renaming h24 → _p2mH24
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
section
namespace AFT.RationalNumerics
open scoped BigOperators
variable {Color : Type*} [Fintype Color] [DecidableEq Color]
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
omit [DecidableEq Color] in
theorem _root_.P2M7374ab17.h14 (reference : Color → ℚ) (mass : Color → Color → ℚ) (first second : Color) :
    (rationalCanonicalPair reference mass first second : ℝ)=
      SafePair.canonicalPair (fun color => (reference color : ℝ)) (fun first second => (mass first second : ℝ)) first second := by
  simp only [rationalCanonicalPair,SafePair.canonicalPair,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_sum]
open _root_.P2M7374ab17 renaming h14 → _p2mH14
set_option maxRecDepth 8192
omit [Fintype Color] in
theorem _root_.P2M7374ab17.h15 (core : Finset Color) (color : Color) : |uniformFiniteProfile core color|≤1 := by
  unfold uniformFiniteProfile
  split_ifs with h
  · rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Finset.one_le_card.mpr ⟨color,h⟩)
  · norm_num
open _root_.P2M7374ab17 renaming h15 → _p2mH15
set_option maxRecDepth 8192
omit [DecidableEq Color] in
theorem _root_.P2M7374ab17.h3 (reference : Color → ℝ) (first second : Color → Color → ℝ) (x y : Color) :
    SafePair.canonicalPair reference (fun x y => first x y-second x y) x y=
      SafePair.canonicalPair reference first x y-SafePair.canonicalPair reference second x y := by
  simp only [SafePair.canonicalPair,Finset.sum_sub_distrib]
  ring
open _root_.P2M7374ab17 renaming h3 → _p2mH3
set_option maxRecDepth 8192
omit [DecidableEq Color] in
theorem _root_.P2M7374ab17.h2 (reference : Color → ℝ) (mass : Color → Color → ℝ) (bound : ℝ)
    (hb : 0≤bound) (href : ∀ color,|reference color|≤1) (hm : ∀ first second,|mass first second|≤bound)
    (first second : Color) : |SafePair.canonicalPair reference mass first second|≤
      ((Fintype.card Color : ℝ)+1)^2*bound := by
  have hcol (second) : |∑ first,mass first second|≤(Fintype.card Color : ℝ)*bound := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun first _ => hm first second)).trans_eq (by simp))
  have hrow (first) : |∑ second,mass first second|≤(Fintype.card Color : ℝ)*bound := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun second _ => hm first second)).trans_eq (by simp))
  have hall : |∑ first,∑ second,mass first second|≤(Fintype.card Color : ℝ)^2*bound := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact (Finset.sum_le_sum (fun first _ => hrow first)).trans_eq (by simp;ring)
  have hfirst : |reference first*(∑ x,mass x second)|≤(Fintype.card Color : ℝ)*bound := by
    rw [abs_mul]
    exact (mul_le_mul (href first) (hcol second) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hsecond : |(∑ y,mass first y)*reference second|≤(Fintype.card Color : ℝ)*bound := by
    rw [abs_mul]
    exact (mul_le_mul (hrow first) (href second) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have htotal : |(∑ x,∑ y,mass x y)*reference first*reference second|≤(Fintype.card Color : ℝ)^2*bound := by
    rw [abs_mul,abs_mul]
    exact (mul_le_mul ((mul_le_mul hall (href first) (abs_nonneg _) (by positivity)).trans_eq (mul_one _))
      (href second) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  unfold SafePair.canonicalPair
  apply (abs_add_le _ _).trans
  apply (add_le_add ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (hm first second) hfirst)) hsecond)) htotal).trans
  ring_nf
  exact le_refl _
open _root_.P2M7374ab17 renaming h2 → _p2mH2
end
open _root_.P2M7374ab17 renaming h2 → _p2mH2
open _root_.P2M7374ab17 renaming h3 → _p2mH3
open _root_.P2M7374ab17 renaming h14 → _p2mH14
open _root_.P2M7374ab17 renaming h15 → _p2mH15
end AFT.RationalNumerics
open _root_.P2M7374ab17 renaming h2 → _p2mH2
open _root_.P2M7374ab17 renaming h3 → _p2mH3
open _root_.P2M7374ab17 renaming h14 → _p2mH14
open _root_.P2M7374ab17 renaming h15 → _p2mH15
namespace AFT.V7Calibration
open GaussianSource RationalNumerics
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
end
end AFT.V7Calibration
end
open _root_.P2M7374ab17 renaming h2 → _p2mH2
open _root_.P2M7374ab17 renaming h15 → _p2mH15
open _root_.P2M7374ab17 renaming h3 → _p2mH3
open _root_.P2M7374ab17 renaming h14 → _p2mH14
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.matrixApply
end AFT.MixedKernel.matrixApply
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.PolynomialFamily
end AFT.RationalNumerics.PolynomialFamily
namespace AFT.RationalNumerics.UniformRationalApproximation
end AFT.RationalNumerics.UniformRationalApproximation
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.twoPoolPairedKernel
end AFT.RepresentedPolynomial.twoPoolPairedKernel
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualAnchorMatrix
end AFT.V7Calibration.actualAnchorMatrix
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyCenterProgram
end AFT.V7Calibration.actualBodyCenterProgram
namespace AFT.V7Calibration.actualBodyCompensationProgram
end AFT.V7Calibration.actualBodyCompensationProgram
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyReciprocalProgram
end AFT.V7Calibration.actualBodyReciprocalProgram
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCoreProgram
end AFT.V7Calibration.actualCoreProgram
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualNormalizedSign
end AFT.V7Calibration.actualNormalizedSign
namespace AFT.V7Calibration.actualNormalizedSignProgram
end AFT.V7Calibration.actualNormalizedSignProgram
namespace AFT.V7Calibration.actualPairedMatrixProgram
end AFT.V7Calibration.actualPairedMatrixProgram
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualPublicAnchorMeanProgram
end AFT.V7Calibration.actualPublicAnchorMeanProgram
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualResponseProgram
end AFT.V7Calibration.actualResponseProgram
namespace AFT.V7Calibration.actualSafeProgram_iff
end AFT.V7Calibration.actualSafeProgram_iff
namespace AFT.V7Calibration.actualSignedSliceMean
end AFT.V7Calibration.actualSignedSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyCompensation
end AFT.V7Calibration.bodyCompensation
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.probabilityClamp
end AFT.V7Calibration.probabilityClamp
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.bodyPublicMatrix
end AFT.bodyPublicMatrix
namespace AFT.pairedPublicDensity
end AFT.pairedPublicDensity
namespace AFT.pairedPublicKernel
end AFT.pairedPublicKernel
namespace AFT.pairedPublicMatrix
end AFT.pairedPublicMatrix
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.publicInputMatrix
end AFT.publicInputMatrix
section
namespace AFT.RationalNumerics
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h13 (colors : ℕ) (reference : ℕ → ℚ) (mass : ℕ → ℕ → ℚ)
    (first second : Fin colors) :
    rationalCanonicalPairProgram colors reference mass first.val second.val=
      rationalCanonicalPair (fun color : Fin colors => reference color.val)
        (fun first second : Fin colors => mass first.val second.val) first second := by
  simp only [rationalCanonicalPairProgram,rationalCanonicalPair,←Fin.sum_univ_eq_sum_range]
open _root_.P2M7374ab17 renaming h13 → _p2mH13
end AFT.RationalNumerics
open _root_.P2M7374ab17 renaming h13 → _p2mH13
end
open _root_.P2M7374ab17 renaming h13 → _p2mH13
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
theorem _root_.P2M7374ab17.h55 (security : ℕ) :
    activation security / 2 ≤ activation security +
      signFunctional (anchorSign security) (signProfile security) :=
  _p2mH29 _ _
    ((signFunctional_abs_le_l1 (anchorSign security) (signProfile security)
      (anchorSign_abs_le_one security)).trans (signProfile_l1_le_half_activation security))
open _root_.P2M7374ab17 renaming h55 → _p2mH55
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h56 (security : ℕ) (profile : Palette security → ℝ) :
    (responseEquiv security).symm profile = profile -
      ((activation security + signFunctional (anchorSign security) (signProfile security))⁻¹ *
        signFunctional (anchorSign security) profile) • signProfile security :=
  _p2mH28 _ _ _ _ _ _
open _root_.P2M7374ab17 renaming h56 → _p2mH56
end
open _root_.P2M7374ab17 renaming h55 → _p2mH55
open _root_.P2M7374ab17 renaming h56 → _p2mH56
end CurrentAFT.FirstResponse
open _root_.P2M7374ab17 renaming h55 → _p2mH55
open _root_.P2M7374ab17 renaming h56 → _p2mH56
end
open _root_.P2M7374ab17 renaming h55 → _p2mH55
open _root_.P2M7374ab17 renaming h56 → _p2mH56
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
theorem _root_.P2M7374ab17.h94 (security : ℕ) (seed : ActualSeed security) :
    (actualSeedLaw security).weight (seedNegate security seed) = (actualSeedLaw security).weight seed := by
  simp only [actualSeedLaw, seedNegate, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, FiniteDist.prod_weight,
    edgeLaw, scalarLaw, GaussianSource.windowGaussian_reflection]
open _root_.P2M7374ab17 renaming h94 → _p2mH94
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h79 (security : ℕ) (seed : ActualSeed security) :
    actualBlur security (seedNegate security seed) = -actualBlur security seed := by
  simp only [actualBlur, seedNegate, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    GaussianSource.windowNegateEquiv_val]
  ring
open _root_.P2M7374ab17 renaming h79 → _p2mH79
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h81 (security : ℕ) (seed : ActualSeed security) :
    actualSecond security (seedNegate security seed) = -actualSecond security seed := rfl
open _root_.P2M7374ab17 renaming h81 → _p2mH81
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h89 (modulus : ℕ) (color : Fin modulus) :
    (color.rev.val : ℤ) = (modulus : ℤ) - 1 - color.val := by
  simp only [Fin.val_rev]
  omega
open _root_.P2M7374ab17 renaming h89 → _p2mH89
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h88 (positive : Bool) (width : ℕ) (blur : ℤ) :
    intervalStart (!positive) width (-blur) =
      TrimmedSlice.reflectedStart (intervalStart positive width blur) width := by
  cases positive <;> simp only [Bool.not_false, Bool.not_true, intervalStart,
    Bool.false_eq_true, if_false, if_true, TrimmedSlice.reflectedStart] <;> ring
open _root_.P2M7374ab17 renaming h88 → _p2mH88
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h80 (security : ℕ) (positive : Bool)
    (color : Fin (Parameters.modulus security)) :
    actualProfile security positive color.rev = actualProfile security (!positive) color := by
  unfold actualProfile profile
  rw [_p2mH89]
  exact _p2mH22 _ _ _
    (fun seed => intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
    (fun seed => intervalStart (!positive) (Parameters.anchorWidth security) (actualBlur security seed))
    (actualSecond security) (actualSeedLaw security).weight (seedNegate security)
    (_p2mH94 security) (_p2mH81 security)
    (fun seed => by rw [_p2mH79, _p2mH88]) _
open _root_.P2M7374ab17 renaming h80 → _p2mH80
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h93 (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (safeLaw security).weight color.rev = (safeLaw security).weight color := by
  rw [safeLaw, TrimmedSlice.finiteLaw_weight, TrimmedSlice.finiteLaw_weight,
    _p2mH89, _p2mH21, neg_zero]
open _root_.P2M7374ab17 renaming h93 → _p2mH93
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h95 (modulus : ℕ) [NeZero modulus] (shift : ℤ) :
    shiftColor modulus (-shift) = -shiftColor modulus shift := by
  simp only [shiftColor, Int.cast_neg, map_neg]
open _root_.P2M7374ab17 renaming h95 → _p2mH95
set_option maxRecDepth 8192
private theorem _root_.P2M7374ab17.h330 (modulus : ℕ) [NeZero modulus] (shift : ℤ) (color : Fin modulus) :
    ((ZMod.finEquiv modulus).toEquiv.trans
      ((Equiv.addRight (shift : ZMod modulus)).trans (ZMod.finEquiv modulus).toEquiv.symm)) color =
        color + shiftColor modulus shift := by
  apply (ZMod.finEquiv modulus).injective
  change (ZMod.finEquiv modulus)
      ((ZMod.finEquiv modulus).symm ((ZMod.finEquiv modulus) color + (shift : ZMod modulus))) = _
  simp only [RingEquiv.apply_symm_apply, map_add, shiftColor]
open _root_.P2M7374ab17 renaming h330 → _p2mH330
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h96 (security : ℕ) (shift : ℤ) (color : Fin (Parameters.modulus security)) :
    shiftEquiv security shift color = color + shiftColor (Parameters.modulus security) shift :=
  _p2mH330 _ _ _
open _root_.P2M7374ab17 renaming h96 → _p2mH96
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h98 (security : ℕ) (shift : ℤ) (color : Fin (Parameters.modulus security)) :
    (shiftEquiv security shift).symm color = shiftEquiv security (-shift) color := by
  apply (shiftEquiv security shift).injective
  rw [Equiv.apply_symm_apply]
  simp only [_p2mH96, _p2mH95]
  abel
open _root_.P2M7374ab17 renaming h98 → _p2mH98
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h97 (security : ℕ) (shift : ℤ) (color : Fin (Parameters.modulus security)) :
    shiftEquiv security (-shift) color.rev = (shiftEquiv security shift color).rev := by
  simp only [_p2mH96, Fin.rev_add, _p2mH95, sub_eq_add_neg]
open _root_.P2M7374ab17 renaming h97 → _p2mH97
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h99 (security : ℕ) (shift : ℤ) (color : Fin (Parameters.modulus security)) :
    (shiftEquiv security (-shift)).symm color.rev = ((shiftEquiv security shift).symm color).rev := by
  simp only [_p2mH98, neg_neg]
  simpa only [neg_neg] using _p2mH97 security (-shift) color
open _root_.P2M7374ab17 renaming h99 → _p2mH99
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h83 (security : ℕ) (includeScalar : Bool) (seed : ActualSeed security) :
    actualBlur security (seedNegate security seed) +
        (if includeScalar then actualSecond security (seedNegate security seed) else 0) =
      -(actualBlur security seed + if includeScalar then actualSecond security seed else 0) := by
  rw [_p2mH79, _p2mH81]
  cases includeScalar <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring
open _root_.P2M7374ab17 renaming h83 → _p2mH83
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h82 (security : ℕ) (includeScalar : Bool)
    (color : Fin (Parameters.modulus security)) :
    (bodyLaw security includeScalar).weight color.rev = (bodyLaw security includeScalar).weight color := by
  unfold bodyLaw
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  calc
    _ = ∑ seed, (actualSeedLaw security).weight (seedNegate security seed) *
        (safeLaw security).weight ((shiftEquiv security
          (actualBlur security (seedNegate security seed) +
            if includeScalar then actualSecond security (seedNegate security seed) else 0)).symm color.rev) :=
      ((seedNegate security).sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro seed _
      rw [_p2mH94, _p2mH83, _p2mH99, _p2mH93]
open _root_.P2M7374ab17 renaming h82 → _p2mH82
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h84 (security : ℕ) (color : Fin (Parameters.modulus security)) :
    diffuseMean security color.rev = diffuseMean security color := by
  simp only [diffuseMean, _p2mH80, Bool.not_true, Bool.not_false]
  ring
open _root_.P2M7374ab17 renaming h84 → _p2mH84
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h92 (security : ℕ) (color : Fin (Parameters.modulus security)) :
    primaryProfile security color.rev = primaryProfile security color := by
  simp only [primaryProfile, _p2mH82, _p2mH84]
open _root_.P2M7374ab17 renaming h92 → _p2mH92
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h91 (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (primaryLaw security).weight color.rev = (primaryLaw security).weight color :=
  _p2mH92 security color
open _root_.P2M7374ab17 renaming h91 → _p2mH91
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h90 (security : ℕ) (color : InwardAnchor.Palette security) (coin : Bool) :
    InwardAnchor.positiveDirection security color.rev (!coin) =
      !(InwardAnchor.positiveDirection security color coin) := by
  have hsum : color.rev.val + color.val = Parameters.modulus security - 1 := by
    simp only [Fin.val_rev]
    omega
  by_cases hlow : 2 * color.val < Parameters.modulus security - 1
  · have hrevhigh : Parameters.modulus security - 1 < 2 * color.rev.val := by omega
    have hrevlow : ¬2 * color.rev.val < Parameters.modulus security - 1 := by omega
    simp only [InwardAnchor.positiveDirection, hlow, hrevhigh, hrevlow, if_true, if_false, Bool.not_false]
  · by_cases hhigh : Parameters.modulus security - 1 < 2 * color.val
    · have hrevlow : 2 * color.rev.val < Parameters.modulus security - 1 := by omega
      simp only [InwardAnchor.positiveDirection, hlow, hhigh, hrevlow, if_true, if_false, Bool.not_true]
    · have hrevlow : ¬2 * color.rev.val < Parameters.modulus security - 1 := by omega
      have hrevhigh : ¬Parameters.modulus security - 1 < 2 * color.rev.val := by omega
      simp only [InwardAnchor.positiveDirection, hlow, hhigh, hrevlow, hrevhigh, if_false]
open _root_.P2M7374ab17 renaming h90 → _p2mH90
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h87 (security : ℕ) (direction : Bool) :
    (directionLaw security).weight (!direction) = (directionLaw security).weight direction := by
  classical
  let reverse := (Fin.revPerm : Equiv.Perm (Fin (Parameters.modulus security))).prodCongr Equiv.boolNot
  have hweight (input : Fin (Parameters.modulus security) × Bool) :
      ((primaryLaw security).prod (FiniteDist.uniform Bool)).weight (reverse input) =
        ((primaryLaw security).prod (FiniteDist.uniform Bool)).weight input := by
    change (primaryLaw security).weight input.1.rev * (FiniteDist.uniform Bool).weight (!input.2) = _
    rw [_p2mH91]
    rfl
  have hdirection (input : Fin (Parameters.modulus security) × Bool) :
      InwardAnchor.positiveDirection security (reverse input).1 (reverse input).2 =
        !(InwardAnchor.positiveDirection security input.1 input.2) :=
    _p2mH90 security input.1 input.2
  unfold directionLaw
  simp only [FiniteDist.map_weight]
  calc
    _ = ∑ input, @ite ℝ
        (InwardAnchor.positiveDirection security (reverse input).1 (reverse input).2 = !direction)
        (Classical.propDecidable _)
        (((primaryLaw security).prod (FiniteDist.uniform Bool)).weight (reverse input)) 0 :=
      (reverse.sum_comp (fun input : Fin (Parameters.modulus security) × Bool =>
        @ite ℝ (InwardAnchor.positiveDirection security input.1 input.2 = !direction)
          (Classical.propDecidable _)
          (((primaryLaw security).prod (FiniteDist.uniform Bool)).weight input) 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro input _
      rw [hweight, hdirection]
      simp only [Bool.not_inj_iff]
      split_ifs <;> rfl
open _root_.P2M7374ab17 renaming h87 → _p2mH87
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h86 (security : ℕ) (direction : Bool) :
    (directionLaw security).weight direction = 1 / 2 := by
  have hsum := (directionLaw security).sum_one
  have hreflection := _p2mH87 security true
  simp only [Fintype.sum_bool] at hsum
  simp only [Bool.not_true] at hreflection
  cases direction <;> linarith
open _root_.P2M7374ab17 renaming h86 → _p2mH86
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h85 (security : ℕ) :
    directionLaw security = FiniteDist.uniform Bool := by
  apply FiniteDist.ext
  intro direction
  rw [_p2mH86]
  simp [FiniteDist.uniform_weight]
open _root_.P2M7374ab17 renaming h85 → _p2mH85
end
open _root_.P2M7374ab17 renaming h79 → _p2mH79
open _root_.P2M7374ab17 renaming h80 → _p2mH80
open _root_.P2M7374ab17 renaming h81 → _p2mH81
open _root_.P2M7374ab17 renaming h82 → _p2mH82
open _root_.P2M7374ab17 renaming h83 → _p2mH83
open _root_.P2M7374ab17 renaming h84 → _p2mH84
open _root_.P2M7374ab17 renaming h85 → _p2mH85
open _root_.P2M7374ab17 renaming h86 → _p2mH86
open _root_.P2M7374ab17 renaming h87 → _p2mH87
open _root_.P2M7374ab17 renaming h88 → _p2mH88
open _root_.P2M7374ab17 renaming h89 → _p2mH89
open _root_.P2M7374ab17 renaming h90 → _p2mH90
open _root_.P2M7374ab17 renaming h91 → _p2mH91
open _root_.P2M7374ab17 renaming h92 → _p2mH92
open _root_.P2M7374ab17 renaming h93 → _p2mH93
open _root_.P2M7374ab17 renaming h94 → _p2mH94
open _root_.P2M7374ab17 renaming h95 → _p2mH95
open _root_.P2M7374ab17 renaming h96 → _p2mH96
open _root_.P2M7374ab17 renaming h97 → _p2mH97
open _root_.P2M7374ab17 renaming h98 → _p2mH98
open _root_.P2M7374ab17 renaming h99 → _p2mH99
open _root_.P2M7374ab17 renaming h330 → _p2mH330
end CurrentAFT.ProposalSymmetry
open _root_.P2M7374ab17 renaming h79 → _p2mH79
open _root_.P2M7374ab17 renaming h80 → _p2mH80
open _root_.P2M7374ab17 renaming h81 → _p2mH81
open _root_.P2M7374ab17 renaming h82 → _p2mH82
open _root_.P2M7374ab17 renaming h83 → _p2mH83
open _root_.P2M7374ab17 renaming h84 → _p2mH84
open _root_.P2M7374ab17 renaming h85 → _p2mH85
open _root_.P2M7374ab17 renaming h86 → _p2mH86
open _root_.P2M7374ab17 renaming h87 → _p2mH87
open _root_.P2M7374ab17 renaming h88 → _p2mH88
open _root_.P2M7374ab17 renaming h89 → _p2mH89
open _root_.P2M7374ab17 renaming h90 → _p2mH90
open _root_.P2M7374ab17 renaming h91 → _p2mH91
open _root_.P2M7374ab17 renaming h92 → _p2mH92
open _root_.P2M7374ab17 renaming h93 → _p2mH93
open _root_.P2M7374ab17 renaming h94 → _p2mH94
open _root_.P2M7374ab17 renaming h95 → _p2mH95
open _root_.P2M7374ab17 renaming h96 → _p2mH96
open _root_.P2M7374ab17 renaming h97 → _p2mH97
open _root_.P2M7374ab17 renaming h98 → _p2mH98
open _root_.P2M7374ab17 renaming h99 → _p2mH99
open _root_.P2M7374ab17 renaming h330 → _p2mH330
end
open _root_.P2M7374ab17 renaming h87 → _p2mH87
open _root_.P2M7374ab17 renaming h91 → _p2mH91
open _root_.P2M7374ab17 renaming h98 → _p2mH98
open _root_.P2M7374ab17 renaming h83 → _p2mH83
open _root_.P2M7374ab17 renaming h95 → _p2mH95
open _root_.P2M7374ab17 renaming h79 → _p2mH79
open _root_.P2M7374ab17 renaming h85 → _p2mH85
open _root_.P2M7374ab17 renaming h89 → _p2mH89
open _root_.P2M7374ab17 renaming h96 → _p2mH96
open _root_.P2M7374ab17 renaming h88 → _p2mH88
open _root_.P2M7374ab17 renaming h82 → _p2mH82
open _root_.P2M7374ab17 renaming h80 → _p2mH80
open _root_.P2M7374ab17 renaming h99 → _p2mH99
open _root_.P2M7374ab17 renaming h84 → _p2mH84
open _root_.P2M7374ab17 renaming h86 → _p2mH86
open _root_.P2M7374ab17 renaming h81 → _p2mH81
open _root_.P2M7374ab17 renaming h93 → _p2mH93
open _root_.P2M7374ab17 renaming h90 → _p2mH90
open _root_.P2M7374ab17 renaming h97 → _p2mH97
open _root_.P2M7374ab17 renaming h94 → _p2mH94
open _root_.P2M7374ab17 renaming h92 → _p2mH92
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
theorem _root_.P2M7374ab17.h46 (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s')
    (colors : Fin (r + r') → Primary) (centers : Fin (s + s') → Body) :
    (homogeneousProduct primary body first second).val colors centers =
      ((r + r').factorial : ℝ)⁻¹ * ((s + s').factorial : ℝ)⁻¹ *
        ∑ primaryOrder : Equiv.Perm (Fin (r + r')), ∑ bodyOrder : Equiv.Perm (Fin (s + s')),
          finDisjointTensor first.val second.val (colors ∘ primaryOrder) (centers ∘ bodyOrder) := by
  exact (symmetrize_apply (finDisjointTensor first.val second.val) colors centers).trans (by
    simp only [Fintype.card_perm, Fintype.card_fin])
open _root_.P2M7374ab17 renaming h46 → _p2mH46
end
open _root_.P2M7374ab17 renaming h46 → _p2mH46
end CurrentAFT.ControlProduct
open _root_.P2M7374ab17 renaming h46 → _p2mH46
end
open _root_.P2M7374ab17 renaming h46 → _p2mH46
section
namespace CurrentAFT.DiffusePairBounds
open AFT AFT.TrimmedSlice AFT.SafeConvolution DiffuseProfiles ProposalPrimary
  ActualControls FirstResponse PairSmoothing DiffusePair BackgroundRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  Parameters.safeMargin ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ActualControls.bodyReference
  DiffusePair.pairProfile DiffusePair.safePairProfile DiffusePair.liftedPairProfile
  DiffusePair.rootPairLaw DiffusePair.rootPairShift
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h49 (security : ℕ) (scalar : ℤ)
    (first second : ActualControls.Palette security) :
    safePairProfile security scalar first second = safePairProfile security scalar second first := by
  have htranspose : (fun first second =>
      AFT.SafePair.restrictPair (safeCore security) (pairProfile security scalar) second first) =
      AFT.SafePair.restrictPair (safeCore security) (pairProfile security scalar) := by
    funext first second
    by_cases hfirst : first ∈ safeCore security <;> by_cases hsecond : second ∈ safeCore security <;>
      simp only [AFT.SafePair.restrictPair, hfirst, hsecond, and_self, and_true, and_false,
        if_true, if_false, pairProfile_symmetric security scalar]
  unfold safePairProfile AFT.SafePair.coreSeed
  rw [AFT.SafePair.canonicalPair_transpose, htranspose]
open _root_.P2M7374ab17 renaming h49 → _p2mH49
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h48 (security : ℕ) (scalar : ℤ) (first second : SafePalette security) :
    bodyPairDensity security scalar first second = bodyPairDensity security scalar second first := by
  rw [bodyPairDensity, bodyPairDensity, _p2mH49, mul_comm]
open _root_.P2M7374ab17 renaming h48 → _p2mH48
end
open _root_.P2M7374ab17 renaming h48 → _p2mH48
open _root_.P2M7374ab17 renaming h49 → _p2mH49
end CurrentAFT.DiffusePairBounds
open _root_.P2M7374ab17 renaming h48 → _p2mH48
open _root_.P2M7374ab17 renaming h49 → _p2mH49
end
open _root_.P2M7374ab17 renaming h49 → _p2mH49
open _root_.P2M7374ab17 renaming h48 → _p2mH48
section
namespace CurrentAFT.PairCertificateFamilies
open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm
  GradedControlStability DiffuseProfiles ProposalPrimary ActualControls
  BackgroundCertificates BackgroundRates BackgroundFamilies DiffusePair DiffusePairBounds
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ActualControls.bodyReference DiffusePairBounds.bodyPairDensity BackgroundRates.bodyFactor
attribute [local instance] _root_.CurrentAFT.PairCertificateFamilies.classicalFinDecidableEq
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
omit [Fintype Primary] [Fintype Body] in
theorem _root_.P2M7374ab17.h78 (density : Body → Body → ℝ)
    (hsymmetric : ∀ first second, density first second = density second first) :
    SeparatelySymmetric (pairBodyRaw (Primary := Primary) density) := by
  intro primaryOrder bodyOrder colors centers
  have hne : (bodyOrder 0).val ≠ (bodyOrder 1).val := by
    intro hequal
    have h := bodyOrder.injective (Fin.ext hequal)
    have hv := congrArg Fin.val h
    norm_num at hv
  have hzero := (bodyOrder 0).isLt
  have hone := (bodyOrder 1).isLt
  have hcases : ((bodyOrder 0).val = 0 ∧ (bodyOrder 1).val = 1) ∨
      ((bodyOrder 0).val = 1 ∧ (bodyOrder 1).val = 0) := by omega
  rcases hcases with hcases | hcases
  · have h0 : bodyOrder 0 = 0 := Fin.ext hcases.1
    have h1 : bodyOrder 1 = 1 := Fin.ext hcases.2
    simp only [pairBodyRaw, Function.comp_apply, h0, h1]
  · have h0 : bodyOrder 0 = 1 := Fin.ext hcases.1
    have h1 : bodyOrder 1 = 0 := Fin.ext hcases.2
    simpa only [pairBodyRaw, Function.comp_apply, h0, h1] using hsymmetric (centers 1) (centers 0)
open _root_.P2M7374ab17 renaming h78 → _p2mH78
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h77 (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Body → Body → ℝ)
    (hfirst : ∀ second, ∑ first, body.weight first * density first second = 0)
    (hsecond : ∀ first, ∑ second, body.weight second * density first second = 0)
    (hsymmetric : ∀ first second, density first second = density second first) :
    (bodyPairKernel primary body density hfirst hsecond).val = pairBodyRaw density :=
  symmetrize_of_symmetric _ (_p2mH78 density hsymmetric)
open _root_.P2M7374ab17 renaming h77 → _p2mH77
end
open _root_.P2M7374ab17 renaming h77 → _p2mH77
open _root_.P2M7374ab17 renaming h78 → _p2mH78
end CurrentAFT.PairCertificateFamilies
open _root_.P2M7374ab17 renaming h77 → _p2mH77
open _root_.P2M7374ab17 renaming h78 → _p2mH78
end
open _root_.P2M7374ab17 renaming h78 → _p2mH78
open _root_.P2M7374ab17 renaming h77 → _p2mH77
section
namespace CurrentAFT.ConditionalPairMean
open AFT DiffuseProfiles ProposalPrimary ActualControls FirstResponse
  LocalReferenceEnergy BackgroundCertificates FringeCertificate
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h43 (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ other, (markedPairAt security primary scalar).weight (output, other)) =
      if primary = output then 1 else 0 := by
  simp only [markedPairAt, FiniteDist.map_weight, Prod.mk.injEq]
  rw [Finset.sum_comm]
  by_cases hprimary : primary = output
  · simp only [hprimary, true_and]
    simp [FiniteDist.sum_one]
  · simp [hprimary]
open _root_.P2M7374ab17 renaming h43 → _p2mH43
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h44 (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ other, (markedPairAt security primary scalar).weight (other, output)) =
      (markedCompanionAt security primary scalar).weight output := by
  simp only [markedPairAt, FiniteDist.map_weight, Prod.mk.injEq]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single output]
  · simp
  · intro other _ hother
    apply Finset.sum_eq_zero
    intro index _
    simp [hother]
  · simp
open _root_.P2M7374ab17 renaming h44 → _p2mH44
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h45 (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    pairMean security scalar output =
      ∑ primary, (primaryLaw security).weight primary *
        ((∑ other, (pairAt security primary scalar).weight (output, other)) +
          ∑ other, (pairAt security primary scalar).weight (other, output)) := by
  simp only [pairAt, Finset.sum_add_distrib, ← Finset.mul_sum,
    _p2mH43, _p2mH44]
  unfold pairMean diffuseFirst diffuseSecond markedSecond
  simp only [FiniteDist.mix_weight, firstMarginal, secondMarginal]
  simp only [mul_add, Finset.sum_add_distrib]
  ring_nf
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring_nf
open _root_.P2M7374ab17 renaming h45 → _p2mH45
end
open _root_.P2M7374ab17 renaming h43 → _p2mH43
open _root_.P2M7374ab17 renaming h44 → _p2mH44
open _root_.P2M7374ab17 renaming h45 → _p2mH45
end CurrentAFT.ConditionalPairMean
open _root_.P2M7374ab17 renaming h43 → _p2mH43
open _root_.P2M7374ab17 renaming h44 → _p2mH44
open _root_.P2M7374ab17 renaming h45 → _p2mH45
end
open _root_.P2M7374ab17 renaming h44 → _p2mH44
open _root_.P2M7374ab17 renaming h45 → _p2mH45
open _root_.P2M7374ab17 renaming h43 → _p2mH43
section
namespace CurrentAFT.GradedInverse
open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h57 (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (family : KernelFamily primary body order)
    (hfirst : VanishesBelow primary body order 1 family) (power : ℕ) :
    VanishesBelow primary body order power (family ^ power) := by
  induction power with
  | zero => exact vanishesBelow_zero primary body order _
  | succ power ih =>
    rw [pow_succ]
    exact vanishesBelow_mul primary body order power 1 _ family ih hfirst
open _root_.P2M7374ab17 renaming h57 → _p2mH57
end
open _root_.P2M7374ab17 renaming h57 → _p2mH57
end CurrentAFT.GradedInverse
open _root_.P2M7374ab17 renaming h57 → _p2mH57
end
open _root_.P2M7374ab17 renaming h57 → _p2mH57
section
namespace CurrentAFT.DiffusePairEvaluation
open AFT AFT.SafeConvolution AFT.SafePair ControlCoordinates LeadingEvaluation
  DiffuseProfiles ProposalPrimary ActualControls PrimaryMassFamilies PairReindex PairSmoothing
  BackgroundEvaluation BodyChannelEvaluation BodyPairEvaluation DiffusePair DiffusePairBounds FringeCertificate
  DiffusePairResidual DiffusePairResidualRates DiffusePairCertificates LocalCoefficientFamily
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  MarkedPairLeading.bodyConvolution DiffusePair.safePairProfile DiffusePairResidual.seedProfile
  DiffusePairResidual.rootResiduePairLaw BodyChannelEvaluation.bodyTensorMass DiffusePairBounds.bodyPairDensity
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h52 (modulus : ℕ) [NeZero modulus] (shift : ZMod modulus) (color : Fin modulus) :
    (cyclicEquiv modulus shift).symm color =
        (ZMod.finEquiv modulus).symm ((ZMod.finEquiv modulus) color - shift) := by
  cases modulus with
  | zero => exact Fin.elim0 color
  | succ modulus =>
      simp [cyclicEquiv, ZMod.finEquiv, Equiv.symm_trans_apply, Equiv.addRight_symm,
        Equiv.coe_addRight, sub_eq_add_neg]
open _root_.P2M7374ab17 renaming h52 → _p2mH52
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h53 (modulus : ℕ) [NeZero modulus]
    {Seed : Type*} [Fintype Seed] (law : FiniteDist Seed) (shift : Seed → ZMod modulus)
    (profile : Fin modulus → Fin modulus → ℝ) (first second : Fin modulus) :
    (∑ left, law.weight left * ∑ right, law.weight right *
      profile ((ZMod.finEquiv modulus).symm ((ZMod.finEquiv modulus) first - shift left))
        ((ZMod.finEquiv modulus).symm ((ZMod.finEquiv modulus) second - shift right))) =
      convolution ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).weight
        (fun color => liftPair (ZMod.finEquiv modulus).toEquiv profile color.1 color.2)
        ((ZMod.finEquiv modulus) first, (ZMod.finEquiv modulus) second) := by
  change _ = ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).expectation
    (fun displacement => liftPair (ZMod.finEquiv modulus).toEquiv profile
      ((ZMod.finEquiv modulus) first - displacement.1) ((ZMod.finEquiv modulus) second - displacement.2))
  rw [FiniteDist.expectation_map, FiniteDist.expectation_prod]
  rfl
open _root_.P2M7374ab17 renaming h53 → _p2mH53
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h51 (modulus : ℕ) [NeZero modulus]
    {Seed : Type*} [Fintype Seed] (law : FiniteDist Seed) (shift : Seed → ZMod modulus)
    (profile : Fin modulus → Fin modulus → ℝ) (first second : Fin modulus) :
    (∑ left, law.weight left * ∑ right, law.weight right *
      profile ((cyclicEquiv modulus (shift left)).symm first)
        ((cyclicEquiv modulus (shift right)).symm second)) =
      convolution ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).weight
        (fun color => liftPair (ZMod.finEquiv modulus).toEquiv profile color.1 color.2)
        ((ZMod.finEquiv modulus) first, (ZMod.finEquiv modulus) second) := by
  simp only [_p2mH52]
  exact _p2mH53 modulus law shift profile first second
open _root_.P2M7374ab17 renaming h51 → _p2mH51
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h50 (security : ℕ) (scalar : ℤ) (first second : ActualControls.Palette security) :
    MarkedPairLeading.bodyConvolution security (fun left =>
      MarkedPairLeading.bodyConvolution security (safePairProfile security scalar left) second) first =
      pullbackPair (Parameters.modulus security)
        (convolution (rootResiduePairLaw security).weight (seedProfile security scalar)) first second := by
  unfold MarkedPairLeading.bodyConvolution BackgroundCertificates.rootConvolutionProfile
  unfold pullbackPair rootResiduePairLaw rootPairLaw rootPairShift seedProfile
  simp only [LinearMap.coe_mk, AddHom.coe_mk, shiftEquiv]
  change (∑ left, (actualSeedLaw security).weight left * ∑ right, (actualSeedLaw security).weight right *
    safePairProfile security scalar
      ((cyclicEquiv (Parameters.modulus security) (actualBlur security left)).symm first)
      ((cyclicEquiv (Parameters.modulus security) (actualBlur security right)).symm second)) = _
  exact _p2mH51 (Parameters.modulus security) (actualSeedLaw security)
    (fun seed => (actualBlur security seed : ZMod (Parameters.modulus security)))
    (safePairProfile security scalar) first second
open _root_.P2M7374ab17 renaming h50 → _p2mH50
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h54 (modulus : ℕ) [NeZero modulus]
    (profile : Fin modulus → Fin modulus → ℝ) :
    pullbackPair modulus (uniformCanonical (fun color =>
      liftPair (ZMod.finEquiv modulus).toEquiv profile color.1 color.2)) =
        canonicalPair (fun _ => 1 / (modulus : ℝ)) profile := by
  have h := canonicalPair_uniform_lift (ZMod.finEquiv modulus).toEquiv profile
  simp only [ZMod.card, Fintype.card_fin] at h
  funext first second
  change canonicalPair (fun _ => 1 / (Fintype.card (ZMod modulus) : ℝ))
      (liftPair (ZMod.finEquiv modulus).toEquiv profile)
      ((ZMod.finEquiv modulus) first) ((ZMod.finEquiv modulus) second) = _
  simp only [ZMod.card]
  rw [h]
  simp only [liftPair]
  cases modulus with
  | zero => exact Fin.elim0 first
  | succ modulus => rfl
open _root_.P2M7374ab17 renaming h54 → _p2mH54
end
open _root_.P2M7374ab17 renaming h50 → _p2mH50
open _root_.P2M7374ab17 renaming h51 → _p2mH51
open _root_.P2M7374ab17 renaming h52 → _p2mH52
open _root_.P2M7374ab17 renaming h53 → _p2mH53
open _root_.P2M7374ab17 renaming h54 → _p2mH54
end CurrentAFT.DiffusePairEvaluation
open _root_.P2M7374ab17 renaming h50 → _p2mH50
open _root_.P2M7374ab17 renaming h51 → _p2mH51
open _root_.P2M7374ab17 renaming h52 → _p2mH52
open _root_.P2M7374ab17 renaming h53 → _p2mH53
open _root_.P2M7374ab17 renaming h54 → _p2mH54
end
open _root_.P2M7374ab17 renaming h50 → _p2mH50
open _root_.P2M7374ab17 renaming h52 → _p2mH52
open _root_.P2M7374ab17 renaming h51 → _p2mH51
open _root_.P2M7374ab17 renaming h53 → _p2mH53
open _root_.P2M7374ab17 renaming h54 → _p2mH54
namespace CurrentAFT
end CurrentAFT
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
theorem _root_.P2M7374ab17.h36 {State : Type*} [Fintype State] (reference : FiniteDist State)
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
open _root_.P2M7374ab17 renaming h36 → _p2mH36
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h30 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
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
  exact _p2mH36 reference (fun pair => kernel pair.1 pair.2) _
    (one_le_pow₀ hbound) (colors, centers) hatom
open _root_.P2M7374ab17 renaming h30 → _p2mH30
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h31 (security r s : ℕ)
    (kernel : DensityKernel (Primary := ActualControls.Palette security) (Body := SafePalette security) r s)
    (colors : Fin r → ActualControls.Palette security) (centers : Fin s → SafePalette security) :
    |kernel colors centers| ≤ (2 * (Parameters.modulus security : ℝ)) ^ (r + s) *
      blockL2 (primaryLaw security) (bodyReference security) kernel := by
  have hq := FirstResponse.modulus_pos security
  have hq1 : (1 : ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.one_le
  apply _p2mH30 _ _ _ (by linarith)
  · intro color
    have h := primaryProfile_atom_lower security color
    have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * (Parameters.modulus security : ℝ))
    simpa only [primaryLaw, mul_one_div_cancel (by positivity : (2 * (Parameters.modulus security : ℝ)) ≠ 0)] using hm
  · intro color
    have hm := mul_le_mul_of_nonneg_left (bodyReference_lower security color)
      (by positivity : 0 ≤ 2 * (Parameters.modulus security : ℝ))
    simpa only [mul_one_div_cancel (by positivity : (2 * (Parameters.modulus security : ℝ)) ≠ 0)] using hm
open _root_.P2M7374ab17 renaming h31 → _p2mH31
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h33 (security : ℕ) : (1 : ℝ) ≤ Parameters.dimension security := by
  have h := (Parameters.dimension_bounds security).1
  have hp := pow_pos (Parameters.base_pos security) 160
  exact_mod_cast (show 1 ≤ Parameters.dimension security by omega)
open _root_.P2M7374ab17 renaming h33 → _p2mH33
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h34 (security : ℕ) :
    1 ≤ (Parameters.dimension security : ℝ) * primaryFactor security := by
  have hd := _p2mH33 security
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
open _root_.P2M7374ab17 renaming h34 → _p2mH34
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h32 (security : ℕ) :
    1 ≤ (Parameters.dimension security : ℝ) * bodyFactor security := by
  have hd := _p2mH33 security
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
open _root_.P2M7374ab17 renaming h32 → _p2mH32
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h35 (security order : ℕ) (family : Family security order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → ActualControls.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(family arity).val colors centers| ≤
      (2 * (Parameters.modulus security : ℝ) * Parameters.dimension security)^order *
        LocalRaisingBounds.coefficientNorm security order family := by
  have hd := _p2mH33 security
  have hp := (RaisingPatternBudget.primaryFactor_pos security).le
  have hb := (RaisingPatternBudget.bodyFactor_pos security).le
  have hn := familyNorm_nonneg (primaryLaw security) (bodyReference security) order _ _ hp hb family
  have hweight : 1 ≤ (Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
      gradeWeight (primaryFactor security) (bodyFactor security) arity.val.1.val arity.val.2.val := by
    have h := one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (_p2mH34 security) (n := arity.val.1.val))
      (one_le_pow₀ (_p2mH32 security) (n := arity.val.2.val))
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
        blockL2 (primaryLaw security) (bodyReference security) (family arity).val := _p2mH31 security _ _ _ _ _
    _ ≤ (2 * (Parameters.modulus security : ℝ))^(arity.val.1.val + arity.val.2.val) *
        ((Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
          LocalRaisingBounds.coefficientNorm security order family) := mul_le_mul_of_nonneg_left hblock (by positivity)
    _ = (2 * (Parameters.modulus security : ℝ) * Parameters.dimension security)^(arity.val.1.val + arity.val.2.val) *
        LocalRaisingBounds.coefficientNorm security order family := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlarge arity.property) hn
open _root_.P2M7374ab17 renaming h35 → _p2mH35
end
open _root_.P2M7374ab17 renaming h30 → _p2mH30
open _root_.P2M7374ab17 renaming h31 → _p2mH31
open _root_.P2M7374ab17 renaming h32 → _p2mH32
open _root_.P2M7374ab17 renaming h33 → _p2mH33
open _root_.P2M7374ab17 renaming h34 → _p2mH34
open _root_.P2M7374ab17 renaming h35 → _p2mH35
open _root_.P2M7374ab17 renaming h36 → _p2mH36
end CurrentAFT.ActualCoordinateBounds
open _root_.P2M7374ab17 renaming h30 → _p2mH30
open _root_.P2M7374ab17 renaming h31 → _p2mH31
open _root_.P2M7374ab17 renaming h32 → _p2mH32
open _root_.P2M7374ab17 renaming h33 → _p2mH33
open _root_.P2M7374ab17 renaming h34 → _p2mH34
open _root_.P2M7374ab17 renaming h35 → _p2mH35
open _root_.P2M7374ab17 renaming h36 → _p2mH36
end
open _root_.P2M7374ab17 renaming h33 → _p2mH33
open _root_.P2M7374ab17 renaming h36 → _p2mH36
open _root_.P2M7374ab17 renaming h30 → _p2mH30
open _root_.P2M7374ab17 renaming h31 → _p2mH31
open _root_.P2M7374ab17 renaming h32 → _p2mH32
open _root_.P2M7374ab17 renaming h34 → _p2mH34
open _root_.P2M7374ab17 renaming h35 → _p2mH35
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
theorem _root_.P2M7374ab17.h41 (security : ℕ) (shift : ℤ) (color : Palette security)
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
open _root_.P2M7374ab17 renaming h41 → _p2mH41
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h38 (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
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
  have hvalue := _p2mH41 security (seed.blur.1.val - seed.blur.2.val)
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
open _root_.P2M7374ab17 renaming h38 → _p2mH38
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h37 (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) (pair : Palette security × Palette security) :
    (markedLaw security primary scalar seed).weight pair =
      if (primary, markedPoint security primary scalar seed) = pair then 1 else 0 := by
  simp [markedLaw, FiniteDist.map_weight, FiniteDist.uniform_weight]
open _root_.P2M7374ab17 renaming h37 → _p2mH37
end
open _root_.P2M7374ab17 renaming h37 → _p2mH37
open _root_.P2M7374ab17 renaming h38 → _p2mH38
open _root_.P2M7374ab17 renaming h41 → _p2mH41
end CurrentAFT.ActualPublicLegCharge
open _root_.P2M7374ab17 renaming h37 → _p2mH37
open _root_.P2M7374ab17 renaming h38 → _p2mH38
open _root_.P2M7374ab17 renaming h41 → _p2mH41
end
open _root_.P2M7374ab17 renaming h38 → _p2mH38
open _root_.P2M7374ab17 renaming h41 → _p2mH41
open _root_.P2M7374ab17 renaming h37 → _p2mH37
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
private theorem _root_.P2M7374ab17.h329 {First Second Output : Type*} [Fintype First] [Fintype Second] [Fintype Output]
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
open _root_.P2M7374ab17 renaming h329 → _p2mH329
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h40 (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (coin : Bool) (blur : BlurSeed security) :
    (FiniteDist.uniform (InwardAnchor.Index security)).mix (fun index =>
      markedLaw security primary scalar ⟨true, coin, index, blur⟩) =
      ((fixedCoinLaw security primary coin (-scalar.val)
        (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)).map
          (shiftEquiv security (blur.1.val - blur.2.val))).map (fun companion => (primary, companion)) := by
  ext pair
  simp only [FiniteDist.mix_weight, _p2mH37, fixedCoinLaw, FiniteDist.map_map, FiniteDist.map_weight,
    markedPoint, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro index _
  split_ifs <;> rfl
open _root_.P2M7374ab17 renaming h40 → _p2mH40
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h39 (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security) :
    (FiniteDist.uniform Bool).mix (fun coin =>
      (FiniteDist.uniform (InwardAnchor.Index security)).mix (fun index =>
        (publicBlurLaw security).mix (fun blur => markedLaw security primary scalar ⟨true, coin, index, blur⟩))) =
          markedPairAt security primary scalar := by
  have hswap (coin : Bool) := _p2mH329 (FiniteDist.uniform (InwardAnchor.Index security)) (publicBlurLaw security)
    (fun index blur => markedLaw security primary scalar ⟨true, coin, index, blur⟩)
  simp_rw [hswap]
  rw [_p2mH329 (FiniteDist.uniform Bool) (publicBlurLaw security)]
  simp_rw [_p2mH40]
  unfold markedPairAt markedCompanionAt shiftedAnchorLaw
  rw [FiniteDist.map_mix]
  apply congrArg (publicBlurLaw security).mix
  funext blur
  rw [FiniteDist.map_mix, FiniteDist.map_mix]
open _root_.P2M7374ab17 renaming h39 → _p2mH39
end
open _root_.P2M7374ab17 renaming h39 → _p2mH39
open _root_.P2M7374ab17 renaming h40 → _p2mH40
open _root_.P2M7374ab17 renaming h329 → _p2mH329
end CurrentAFT.ActualPublicLegCharge
open _root_.P2M7374ab17 renaming h39 → _p2mH39
open _root_.P2M7374ab17 renaming h40 → _p2mH40
open _root_.P2M7374ab17 renaming h329 → _p2mH329
end
open _root_.P2M7374ab17 renaming h39 → _p2mH39
open _root_.P2M7374ab17 renaming h40 → _p2mH40
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
theorem _root_.P2M7374ab17.h42 {State : Type*} [Fintype State]
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
open _root_.P2M7374ab17 renaming h42 → _p2mH42
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
end
open _root_.P2M7374ab17 renaming h42 → _p2mH42
end CurrentAFT.CalibrationCoordinateError
open _root_.P2M7374ab17 renaming h42 → _p2mH42
end
open _root_.P2M7374ab17 renaming h42 → _p2mH42
section
namespace CurrentAFT.WindowGaussianSampler
open AFT GaussianSource RationalNumerics DiffuseProfiles
open scoped BigOperators Classical
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h327 (security : ℕ) : 0 < squaredWidth security := by
  unfold squaredWidth
  positivity
open _root_.P2M7374ab17 renaming h327 → _p2mH327
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h328 (security : ℕ) :
    (squaredWidth security : ℝ) = (Parameters.sourceWidth security : ℝ)^2 := by
  unfold squaredWidth Parameters.sourceWidth Parameters.base
  push_cast
  rfl
open _root_.P2M7374ab17 renaming h328 → _p2mH328
noncomputable section
end
end CurrentAFT.WindowGaussianSampler
open _root_.P2M7374ab17 renaming h327 → _p2mH327
open _root_.P2M7374ab17 renaming h328 → _p2mH328
end
open _root_.P2M7374ab17 renaming h328 → _p2mH328
open _root_.P2M7374ab17 renaming h327 → _p2mH327
namespace AFT.FiniteDist.joint
end AFT.FiniteDist.joint
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
theorem _root_.P2M7374ab17.h47 {State : Type*} [Fintype State] (first second : FiniteDist State)
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
open _root_.P2M7374ab17 renaming h47 → _p2mH47
end
open _root_.P2M7374ab17 renaming h47 → _p2mH47
end CurrentAFT.CyclePatternProgram
open _root_.P2M7374ab17 renaming h47 → _p2mH47
end
open _root_.P2M7374ab17 renaming h47 → _p2mH47
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
theorem _root_.P2M7374ab17.h62 (security colors width cutoff bits primary : ℕ)
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
open _root_.P2M7374ab17 renaming h62 → _p2mH62
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h59 (security : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) (blur : BlurSeed security) (coin : Bool) :
    (coinEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
      (blur.1.val - blur.2.val) coin first.val second.val : ℝ) =
      (FirstHistogram.diffuseSeedPair security (InwardAnchor.positiveDirection security primary coin) (blur, source)).weight
        (first, second) := by
  rw [FirstHistogram.diffuseSeedPair_weight]
  unfold coinEntry
  rw [_p2mH24]
  rfl
open _root_.P2M7374ab17 renaming h59 → _p2mH59
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h58 (colors width primary : ℕ) (source : ℤ) (first second : ℕ) (blur : ℤ) :
    |(blurEntry colors width primary source first second blur : ℝ)| ≤ 1 := by
  have htrue := _p2mH23 colors 1
    ((if direction colors primary true then (width : ℤ) else -2 * (width : ℤ) + 1) + blur) source width first second
  have hfalse := _p2mH23 colors 1
    ((if direction colors primary false then (width : ℤ) else -2 * (width : ℤ) + 1) + blur) source width first second
  unfold blurEntry
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
  change (|(coinEntry colors width primary source blur true first second : ℝ)| +
    |(coinEntry colors width primary source blur false first second : ℝ)|) / 2 ≤ 1
  change |(coinEntry colors width primary source blur true first second : ℝ)| ≤ 1 at htrue
  change |(coinEntry colors width primary source blur false first second : ℝ)| ≤ 1 at hfalse
  linarith only [htrue, hfalse]
open _root_.P2M7374ab17 renaming h58 → _p2mH58
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h61 (security colors width cutoff bits primary : ℕ) (source : ℤ) (first second : ℕ) :
    (evaluate security colors width cutoff bits primary source first second : ℝ) =
      ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits).prod
        (windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits)).expectation
          (fun blur => (blurEntry colors width primary source first second (blur.1.val - blur.2.val) : ℝ)) := by
  simp only [_p2mH62, Rat.cast_sum, Rat.cast_mul, FiniteDist.expectation,
    FiniteDist.prod_weight, Fintype.sum_prod_type, windowApproxLaw]
open _root_.P2M7374ab17 renaming h61 → _p2mH61
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h64 (security : ℕ) (primary first second : FirstHistogram.Palette security)
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
  simp only [blurEntry, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, _p2mH59,
    FiniteDist.expectation, Fintype.sum_bool, FiniteDist.uniform_weight, Fintype.card_bool, Nat.cast_ofNat]
  ring
open _root_.P2M7374ab17 renaming h64 → _p2mH64
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h63 (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    |(evaluate security (Parameters.modulus security) (Parameters.anchorWidth security) (edgeCutoff security)
      bits primary.val source.val first.val second.val : ℝ) -
        (diffusePairAt security primary source).weight (first, second)| ≤ 2 / (2 : ℝ)^bits := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits
  have hscalar : (∑ point, |approximate.weight point - (edgeLaw security).weight point|) ≤ 1 / (2 : ℝ)^bits :=
    _p2mH16 _ _ _ _ (_p2mH327 security)
      (_p2mH328 security).symm
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
        congrArg abs (congrArg₂ (· - ·) (_p2mH61 _ _ _ _ _ _ _ _ _)
          (_p2mH64 security primary first second source).symm)
    _ ≤ _ := (_p2mH47 _ _ _ 1
      (fun blur => _p2mH58 _ _ _ _ _ _ _)).trans (by simpa only [one_mul] using hl1)
open _root_.P2M7374ab17 renaming h63 → _p2mH63
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h60 (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    |(current security bits primary.val source.val first.val second.val : ℝ) -
      (diffusePairAt security primary source).weight (first, second)| ≤ 2 / (2 : ℝ)^bits := by
  have hwidth : (security + 2)^48 = Parameters.anchorWidth security := by
    simp only [DiffuseProfiles.anchorWidth_eq, Parameters.base]
  have hcutoff : ((security + 2)^2 - 1) / 2 = edgeCutoff security := by
    simp only [edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  unfold current
  rw [PublicParameterProgram.modulus_value, hwidth, hcutoff]
  exact _p2mH63 security bits primary first second source
open _root_.P2M7374ab17 renaming h60 → _p2mH60
end
open _root_.P2M7374ab17 renaming h58 → _p2mH58
open _root_.P2M7374ab17 renaming h59 → _p2mH59
open _root_.P2M7374ab17 renaming h60 → _p2mH60
open _root_.P2M7374ab17 renaming h61 → _p2mH61
open _root_.P2M7374ab17 renaming h62 → _p2mH62
open _root_.P2M7374ab17 renaming h63 → _p2mH63
open _root_.P2M7374ab17 renaming h64 → _p2mH64
end CurrentAFT.LocalDiffuseProgram
open _root_.P2M7374ab17 renaming h58 → _p2mH58
open _root_.P2M7374ab17 renaming h59 → _p2mH59
open _root_.P2M7374ab17 renaming h60 → _p2mH60
open _root_.P2M7374ab17 renaming h61 → _p2mH61
open _root_.P2M7374ab17 renaming h62 → _p2mH62
open _root_.P2M7374ab17 renaming h63 → _p2mH63
open _root_.P2M7374ab17 renaming h64 → _p2mH64
end
open _root_.P2M7374ab17 renaming h62 → _p2mH62
open _root_.P2M7374ab17 renaming h64 → _p2mH64
open _root_.P2M7374ab17 renaming h59 → _p2mH59
open _root_.P2M7374ab17 renaming h61 → _p2mH61
open _root_.P2M7374ab17 renaming h63 → _p2mH63
open _root_.P2M7374ab17 renaming h58 → _p2mH58
open _root_.P2M7374ab17 renaming h60 → _p2mH60
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
theorem _root_.P2M7374ab17.h70 (security colors width cutoff bits primary : ℕ)
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
open _root_.P2M7374ab17 renaming h70 → _p2mH70
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h73 (colors width primary : ℕ) (source blur : ℤ) (coin : Bool)
    (index : Fin width) (first second : ℕ) :
    |(pointEntry colors width primary source blur coin index first second : ℝ)| ≤ 1 := by
  unfold pointEntry
  split_ifs <;> norm_num
open _root_.P2M7374ab17 renaming h73 → _p2mH73
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h66 (colors width primary : ℕ) (source blur : ℤ) (coin : Bool) (first second : ℕ) :
    |(coinEntry colors width primary source blur coin first second : ℝ)| ≤ 1 := by
  by_cases hw : width = 0
  · simp [coinEntry, hw]
  have hwR : (width : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hw
  have hsum : |∑ index : Fin width, (pointEntry colors width primary source blur coin index first second : ℝ)| ≤ width := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _index : Fin width, (1 : ℝ) := Finset.sum_le_sum (fun index _ => _p2mH73 _ _ _ _ _ _ index _ _)
      _ = _ := by simp
  simp only [coinEntry, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum, abs_mul,
    abs_inv, abs_of_nonneg (Nat.cast_nonneg width : (0 : ℝ) ≤ width)]
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))).trans_eq
    (inv_mul_cancel₀ hwR)
open _root_.P2M7374ab17 renaming h66 → _p2mH66
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h65 (colors width primary : ℕ) (source : ℤ) (first second : ℕ) (blur : ℤ) :
    |(blurEntry colors width primary source first second blur : ℝ)| ≤ 1 := by
  have ht := _p2mH66 colors width primary source blur true first second
  have hf := _p2mH66 colors width primary source blur false first second
  unfold blurEntry
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
  linarith only [ht, hf]
open _root_.P2M7374ab17 renaming h65 → _p2mH65
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h74 (security : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) (blur : BlurSeed security) (coin : Bool)
    (index : InwardAnchor.Index security) :
    (pointEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
      (blur.1.val - blur.2.val) coin index first.val second.val : ℝ) =
      (markedLaw security primary source ⟨true, coin, index, blur⟩).weight (first, second) := by
  rw [_p2mH37]
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
    rw [_p2mH38, hvalue]
  simp only [pointEntry, hpoint, Prod.mk.injEq, Fin.ext_iff]
  split_ifs <;> norm_num
open _root_.P2M7374ab17 renaming h74 → _p2mH74
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h67 (security : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) (blur : BlurSeed security) (coin : Bool) :
    (coinEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
      (blur.1.val - blur.2.val) coin first.val second.val : ℝ) =
      (FiniteDist.uniform (InwardAnchor.Index security)).expectation (fun index =>
        (markedLaw security primary source ⟨true, coin, index, blur⟩).weight (first, second)) := by
  simp only [coinEntry, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum,
    _p2mH74, FiniteDist.expectation, FiniteDist.uniform_weight, Fintype.card_fin,
    Finset.mul_sum]
open _root_.P2M7374ab17 renaming h67 → _p2mH67
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h69 (security colors width cutoff bits primary : ℕ) (source : ℤ) (first second : ℕ) :
    (evaluate security colors width cutoff bits primary source first second : ℝ) =
      ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits).prod
        (windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits)).expectation
          (fun blur => (blurEntry colors width primary source first second (blur.1.val - blur.2.val) : ℝ)) := by
  simp only [_p2mH70, Rat.cast_sum, Rat.cast_mul, FiniteDist.expectation,
    FiniteDist.prod_weight, Fintype.sum_prod_type, windowApproxLaw]
open _root_.P2M7374ab17 renaming h69 → _p2mH69
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h72 (security : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    (publicBlurLaw security).expectation (fun blur =>
      (blurEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
        first.val second.val (blur.1.val - blur.2.val) : ℝ)) =
      (markedPairAt security primary source).weight (first, second) := by
  rw [← _p2mH39]
  change _ = (FiniteDist.uniform Bool).expectation (fun coin =>
    (FiniteDist.uniform (InwardAnchor.Index security)).expectation (fun index =>
      (publicBlurLaw security).expectation (fun blur =>
        (markedLaw security primary source ⟨true, coin, index, blur⟩).weight (first, second))))
  simp_rw [FiniteDist.expectation_comm (FiniteDist.uniform (InwardAnchor.Index security)) (publicBlurLaw security)]
  rw [FiniteDist.expectation_comm (FiniteDist.uniform Bool) (publicBlurLaw security)]
  apply congrArg (FiniteDist.expectation (publicBlurLaw security))
  funext blur
  simp only [blurEntry, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, _p2mH67,
    FiniteDist.expectation, Fintype.sum_bool, FiniteDist.uniform_weight, Fintype.card_bool, Nat.cast_ofNat]
  ring
open _root_.P2M7374ab17 renaming h72 → _p2mH72
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h71 (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    |(evaluate security (Parameters.modulus security) (Parameters.anchorWidth security) (edgeCutoff security)
      bits primary.val source.val first.val second.val : ℝ) -
        (markedPairAt security primary source).weight (first, second)| ≤ 2 / (2 : ℝ)^bits := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits
  have hscalar : (∑ point, |approximate.weight point - (edgeLaw security).weight point|) ≤ 1 / (2 : ℝ)^bits :=
    _p2mH16 _ _ _ _ (_p2mH327 security)
      (_p2mH328 security).symm
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
        congrArg abs (congrArg₂ (· - ·) (_p2mH69 _ _ _ _ _ _ _ _ _)
          (_p2mH72 security primary first second source).symm)
    _ ≤ _ := (_p2mH47 _ _ _ 1
      (fun blur => _p2mH65 _ _ _ _ _ _ _)).trans (by simpa only [one_mul] using hl1)
open _root_.P2M7374ab17 renaming h71 → _p2mH71
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h68 (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    |(current security bits primary.val source.val first.val second.val : ℝ) -
      (markedPairAt security primary source).weight (first, second)| ≤ 2 / (2 : ℝ)^bits := by
  have hwidth : (security + 2)^48 = Parameters.anchorWidth security := by
    simp only [DiffuseProfiles.anchorWidth_eq, Parameters.base]
  have hcutoff : ((security + 2)^2 - 1) / 2 = edgeCutoff security := by
    simp only [edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  unfold current
  rw [PublicParameterProgram.modulus_value, hwidth, hcutoff]
  exact _p2mH71 security bits primary first second source
open _root_.P2M7374ab17 renaming h68 → _p2mH68
end
open _root_.P2M7374ab17 renaming h65 → _p2mH65
open _root_.P2M7374ab17 renaming h66 → _p2mH66
open _root_.P2M7374ab17 renaming h67 → _p2mH67
open _root_.P2M7374ab17 renaming h68 → _p2mH68
open _root_.P2M7374ab17 renaming h69 → _p2mH69
open _root_.P2M7374ab17 renaming h70 → _p2mH70
open _root_.P2M7374ab17 renaming h71 → _p2mH71
open _root_.P2M7374ab17 renaming h72 → _p2mH72
open _root_.P2M7374ab17 renaming h73 → _p2mH73
open _root_.P2M7374ab17 renaming h74 → _p2mH74
end CurrentAFT.LocalMarkedProgram
open _root_.P2M7374ab17 renaming h65 → _p2mH65
open _root_.P2M7374ab17 renaming h66 → _p2mH66
open _root_.P2M7374ab17 renaming h67 → _p2mH67
open _root_.P2M7374ab17 renaming h68 → _p2mH68
open _root_.P2M7374ab17 renaming h69 → _p2mH69
open _root_.P2M7374ab17 renaming h70 → _p2mH70
open _root_.P2M7374ab17 renaming h71 → _p2mH71
open _root_.P2M7374ab17 renaming h72 → _p2mH72
open _root_.P2M7374ab17 renaming h73 → _p2mH73
open _root_.P2M7374ab17 renaming h74 → _p2mH74
end
open _root_.P2M7374ab17 renaming h71 → _p2mH71
open _root_.P2M7374ab17 renaming h70 → _p2mH70
open _root_.P2M7374ab17 renaming h65 → _p2mH65
open _root_.P2M7374ab17 renaming h69 → _p2mH69
open _root_.P2M7374ab17 renaming h66 → _p2mH66
open _root_.P2M7374ab17 renaming h74 → _p2mH74
open _root_.P2M7374ab17 renaming h67 → _p2mH67
open _root_.P2M7374ab17 renaming h73 → _p2mH73
open _root_.P2M7374ab17 renaming h72 → _p2mH72
open _root_.P2M7374ab17 renaming h68 → _p2mH68
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
theorem _root_.P2M7374ab17.h75 (security bits : ℕ) :
    |(activationApprox security bits : ℝ) - DiffuseProfiles.activation security| ≤ (1/2:ℝ) * (1 / (2:ℝ)^bits) := by
  let law := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits
  have hsum : (∑ point, |law.weight point - (scalarLaw security).weight point|) ≤ 1 / (2:ℝ)^bits :=
    _p2mH16 _ _ _ _ (_p2mH327 security)
      (_p2mH328 security).symm
  have hatom := Finset.single_le_sum (f := fun point => |law.weight point - (scalarLaw security).weight point|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ (windowZero (Parameters.sourceCutoff security - 1)))
  have heq : (activationApprox security bits : ℝ) = (1/2:ℝ)*law.weight (windowZero _) := by
    simp only [activationApprox, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    rfl
  rw [heq]
  unfold DiffuseProfiles.activation
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  exact mul_le_mul_of_nonneg_left (hatom.trans hsum) (by norm_num)
open _root_.P2M7374ab17 renaming h75 → _p2mH75
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h76 (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
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
  have hd := _p2mH60 security bits primary first second source
  have hm := _p2mH68 security bits primary first second source
  have ha := _p2mH75 security bits
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
open _root_.P2M7374ab17 renaming h76 → _p2mH76
end
open _root_.P2M7374ab17 renaming h75 → _p2mH75
open _root_.P2M7374ab17 renaming h76 → _p2mH76
end CurrentAFT.LocalPairProgram
open _root_.P2M7374ab17 renaming h75 → _p2mH75
open _root_.P2M7374ab17 renaming h76 → _p2mH76
end
open _root_.P2M7374ab17 renaming h76 → _p2mH76
open _root_.P2M7374ab17 renaming h75 → _p2mH75
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
theorem _root_.P2M7374ab17.h194 (r s : ℕ) (value : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℚ) :
    ((average r s value : ℚ) : ℝ) = average r s (fun first second => (value first second : ℝ)) := by
  simp only [average, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum]
open _root_.P2M7374ab17 renaming h194 → _p2mH194
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h204 {Primary Body : Type*} {r s r' s' : ℕ}
    (first : Kernel ℚ Primary Body r s) (second : Kernel ℚ Primary Body r' s')
    (colors : Fin (r+r') → Primary) (centers : Fin (s+s') → Body) :
    ((homogeneous first second colors centers : ℚ) : ℝ) =
      homogeneous (fun colors centers => (first colors centers : ℝ))
        (fun colors centers => (second colors centers : ℝ)) colors centers := by
  rw [homogeneous, _p2mH194]
  simp only [tensor, Rat.cast_mul, homogeneous]
open _root_.P2M7374ab17 renaming h204 → _p2mH204
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h214 {Primary Body : Type*} (order : ℕ) (first second : Table ℚ Primary Body order) :
    realTable order (product order first second) = product order (realTable order first) (realTable order second) := by
  funext output colors centers
  simp only [realTable, product, Rat.cast_sum]
  apply Finset.sum_congr (by ext left; simp)
  intro left _
  apply Finset.sum_congr (by ext right; simp)
  intro right _
  split_ifs with hmatch
  · exact _p2mH204 (first left) (second right) _ _
  · exact Rat.cast_zero
open _root_.P2M7374ab17 renaming h214 → _p2mH214
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h202 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) {r s r' s' : ℕ}
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s') :
    homogeneous first.val second.val = (homogeneousProduct primary body first second).val := by
  funext colors centers
  rw [_p2mH46]
  unfold homogeneous average
  apply congrArg (fun total : ℝ => ((r+r').factorial : ℝ)⁻¹ * ((s+s').factorial : ℝ)⁻¹ * total)
  apply Finset.sum_congr (by ext first; simp)
  intro firstOrder _
  apply Finset.sum_congr (by ext second; simp)
  intro secondOrder _
  rfl
open _root_.P2M7374ab17 renaming h202 → _p2mH202
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h212 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
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
  · rw [_p2mH202, transportKernel_val]
    rfl
  · rfl
open _root_.P2M7374ab17 renaming h212 → _p2mH212
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h193 (r s : ℕ)
    (value : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℝ) (bound : ℝ)
    (hvalue : ∀ first second, |value first second| ≤ bound) : |average r s value| ≤ bound := by
  have h := _p2mH42
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
open _root_.P2M7374ab17 renaming h193 → _p2mH193
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h195 (r s : ℕ) (first second : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℝ) :
    average r s first - average r s second = average r s (fun p b => first p b - second p b) := by
  simp only [average, Finset.sum_sub_distrib, mul_sub]
open _root_.P2M7374ab17 renaming h195 → _p2mH195
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h206 (first second computedFirst computedSecond A B e f : ℝ)
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
open _root_.P2M7374ab17 renaming h206 → _p2mH206
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h203 {Primary Body : Type*} {r s r' s' : ℕ}
    (first : Kernel ℝ Primary Body r s) (second : Kernel ℝ Primary Body r' s')
    (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (ha : ∀ colors centers, |first colors centers| ≤ A)
    (hb : ∀ colors centers, |second colors centers| ≤ B)
    (colors : Fin (r+r') → Primary) (centers : Fin (s+s') → Body) :
    |homogeneous first second colors centers| ≤ A*B := by
  apply _p2mH193
  intro p b
  unfold tensor
  rw [abs_mul]
  exact mul_le_mul (ha _ _) (hb _ _) (abs_nonneg _) hA
open _root_.P2M7374ab17 renaming h203 → _p2mH203
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h205 {Primary Body : Type*} {r s r' s' : ℕ}
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
  rw [_p2mH195]
  apply _p2mH193
  intro p b
  exact _p2mH206 _ _ _ _ A B e f hA hB he hf (ha _ _) (hb _ _) (hea _ _) (heb _ _)
open _root_.P2M7374ab17 renaming h205 → _p2mH205
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h215 {Primary Body : Type*} (order : ℕ)
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
      · exact _p2mH205 _ _ _ _ A B e f hA hB he hf (ha left) (hb right) (hea left) (heb right) _ _
      · simp only [sub_self, abs_zero]
        positivity
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
open _root_.P2M7374ab17 renaming h215 → _p2mH215
end
open _root_.P2M7374ab17 renaming h193 → _p2mH193
open _root_.P2M7374ab17 renaming h194 → _p2mH194
open _root_.P2M7374ab17 renaming h195 → _p2mH195
open _root_.P2M7374ab17 renaming h202 → _p2mH202
open _root_.P2M7374ab17 renaming h203 → _p2mH203
open _root_.P2M7374ab17 renaming h204 → _p2mH204
open _root_.P2M7374ab17 renaming h205 → _p2mH205
open _root_.P2M7374ab17 renaming h206 → _p2mH206
open _root_.P2M7374ab17 renaming h212 → _p2mH212
open _root_.P2M7374ab17 renaming h214 → _p2mH214
open _root_.P2M7374ab17 renaming h215 → _p2mH215
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M7374ab17 renaming h193 → _p2mH193
open _root_.P2M7374ab17 renaming h194 → _p2mH194
open _root_.P2M7374ab17 renaming h195 → _p2mH195
open _root_.P2M7374ab17 renaming h202 → _p2mH202
open _root_.P2M7374ab17 renaming h203 → _p2mH203
open _root_.P2M7374ab17 renaming h204 → _p2mH204
open _root_.P2M7374ab17 renaming h205 → _p2mH205
open _root_.P2M7374ab17 renaming h206 → _p2mH206
open _root_.P2M7374ab17 renaming h212 → _p2mH212
open _root_.P2M7374ab17 renaming h214 → _p2mH214
open _root_.P2M7374ab17 renaming h215 → _p2mH215
end
open _root_.P2M7374ab17 renaming h193 → _p2mH193
open _root_.P2M7374ab17 renaming h206 → _p2mH206
open _root_.P2M7374ab17 renaming h204 → _p2mH204
open _root_.P2M7374ab17 renaming h205 → _p2mH205
open _root_.P2M7374ab17 renaming h194 → _p2mH194
open _root_.P2M7374ab17 renaming h214 → _p2mH214
open _root_.P2M7374ab17 renaming h212 → _p2mH212
open _root_.P2M7374ab17 renaming h202 → _p2mH202
open _root_.P2M7374ab17 renaming h203 → _p2mH203
open _root_.P2M7374ab17 renaming h215 → _p2mH215
open _root_.P2M7374ab17 renaming h195 → _p2mH195
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT RationalNumerics GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h213 {Primary Body : Type*} (order : ℕ)
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
      · exact _p2mH203 _ _ A B hA hB (ha left) (hb right) _ _
      · simpa only [abs_zero] using mul_nonneg hA hB
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
open _root_.P2M7374ab17 renaming h213 → _p2mH213
end
open _root_.P2M7374ab17 renaming h213 → _p2mH213
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M7374ab17 renaming h213 → _p2mH213
end
open _root_.P2M7374ab17 renaming h213 → _p2mH213
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
theorem _root_.P2M7374ab17.h222 {Primary Body : Type*} (order : ℕ) :
    realTable order (unit (Scalar := ℚ) (Primary := Primary) (Body := Body) order) = unit order := by
  funext arity colors centers
  simp only [realTable, unit, apply_ite, Rat.cast_one, Rat.cast_zero]
  split_ifs <;> rfl
open _root_.P2M7374ab17 renaming h222 → _p2mH222
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h209 {Primary Body : Type*} (order : ℕ) (table : Table ℚ Primary Body order) (count : ℕ) :
    realTable order (power order table count) = power order (realTable order table) count := by
  induction count with
  | zero => exact _p2mH222 order
  | succ count ih => simp only [power, _p2mH214, ih]
open _root_.P2M7374ab17 renaming h209 → _p2mH209
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h197 {Primary Body : Type*} (order population : ℕ) (table : Table ℚ Primary Body order) :
    realTable order (binomial order population table) = binomial order population (realTable order table) := by
  funext arity colors centers
  simp only [realTable, binomial, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast]
  apply Finset.sum_congr rfl
  intro count _
  congr 1
  exact congrFun (congrFun (congrFun (_p2mH209 order table count) arity) colors) centers
open _root_.P2M7374ab17 renaming h197 → _p2mH197
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h220 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
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
open _root_.P2M7374ab17 renaming h220 → _p2mH220
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h207 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order count : ℕ)
    (family : KernelFamily primary body order) :
    power order (fun arity => (family arity).val) count = fun arity => ((family^count) arity).val := by
  induction count with
  | zero => exact _p2mH220 primary body order
  | succ count ih =>
      rw [power, ih, _p2mH212, pow_succ]
      rfl
open _root_.P2M7374ab17 renaming h207 → _p2mH207
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h211 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) (hzero : family (zeroArity order) = 0)
    (count : ℕ) (hcount : order < count) : family^count = 0 := by
  have h := _p2mH57 primary body order family
    (vanishesBelow_one_of_zero primary body order family hzero) count
  funext arity
  exact h arity (by have := arity.property; omega)
open _root_.P2M7374ab17 renaming h211 → _p2mH211
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h199 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order population : ℕ)
    (family : KernelFamily primary body order) (hzero : family (zeroArity order) = 0) :
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
    rw [_p2mH211 primary body order family hzero count hlarge, smul_zero]
open _root_.P2M7374ab17 renaming h199 → _p2mH199
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h196 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order population : ℕ)
    (family : KernelFamily primary body order) (hzero : family (zeroArity order) = 0) :
    binomial order population (fun arity => (family arity).val) =
      fun arity => (((1 + family)^population) arity).val := by
  rw [_p2mH199 primary body order population family hzero]
  funext arity colors centers
  simp only [binomial, _p2mH207, Finset.sum_apply, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro count _
  change _ = population.choose count • (((family^count) arity).val colors centers)
  rw [nsmul_eq_mul]
open _root_.P2M7374ab17 renaming h196 → _p2mH196
end
open _root_.P2M7374ab17 renaming h196 → _p2mH196
open _root_.P2M7374ab17 renaming h197 → _p2mH197
open _root_.P2M7374ab17 renaming h199 → _p2mH199
open _root_.P2M7374ab17 renaming h207 → _p2mH207
open _root_.P2M7374ab17 renaming h209 → _p2mH209
open _root_.P2M7374ab17 renaming h211 → _p2mH211
open _root_.P2M7374ab17 renaming h220 → _p2mH220
open _root_.P2M7374ab17 renaming h222 → _p2mH222
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M7374ab17 renaming h196 → _p2mH196
open _root_.P2M7374ab17 renaming h197 → _p2mH197
open _root_.P2M7374ab17 renaming h199 → _p2mH199
open _root_.P2M7374ab17 renaming h207 → _p2mH207
open _root_.P2M7374ab17 renaming h209 → _p2mH209
open _root_.P2M7374ab17 renaming h211 → _p2mH211
open _root_.P2M7374ab17 renaming h220 → _p2mH220
open _root_.P2M7374ab17 renaming h222 → _p2mH222
end
open _root_.P2M7374ab17 renaming h220 → _p2mH220
open _root_.P2M7374ab17 renaming h197 → _p2mH197
open _root_.P2M7374ab17 renaming h207 → _p2mH207
open _root_.P2M7374ab17 renaming h211 → _p2mH211
open _root_.P2M7374ab17 renaming h196 → _p2mH196
open _root_.P2M7374ab17 renaming h222 → _p2mH222
open _root_.P2M7374ab17 renaming h199 → _p2mH199
open _root_.P2M7374ab17 renaming h209 → _p2mH209
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
variable {Scalar Primary Body Primary' Body' : Type*}
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h219 [Zero Scalar] [One Scalar] (order : ℕ)
    (primary : Primary' → Primary) (body : Body' → Body) :
    pullback order primary body (unit (Scalar := Scalar) order) = unit order := rfl
open _root_.P2M7374ab17 renaming h219 → _p2mH219
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h218 [Field Scalar] (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
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
open _root_.P2M7374ab17 renaming h218 → _p2mH218
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h217 [Field Scalar] (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
    (table : Table Scalar Primary Body order) (count : ℕ) :
    pullback order primary body (power order table count) =
      power order (pullback order primary body table) count := by
  induction count with
  | zero => exact _p2mH219 order primary body
  | succ count ih => simp only [power, _p2mH218, ih]
open _root_.P2M7374ab17 renaming h217 → _p2mH217
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h216 [Field Scalar] (order population : ℕ)
    (primary : Primary' → Primary) (body : Body' → Body) (table : Table Scalar Primary Body order) :
    pullback order primary body (binomial order population table) =
      binomial order population (pullback order primary body table) := by
  funext arity colors centers
  unfold binomial
  change (∑ count ∈ Finset.range (order+1), (population.choose count : Scalar) *
    pullback order primary body (power order table count) arity colors centers) = _
  simp only [_p2mH217]
open _root_.P2M7374ab17 renaming h216 → _p2mH216
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M7374ab17 renaming h216 → _p2mH216
open _root_.P2M7374ab17 renaming h217 → _p2mH217
open _root_.P2M7374ab17 renaming h218 → _p2mH218
open _root_.P2M7374ab17 renaming h219 → _p2mH219
end
open _root_.P2M7374ab17 renaming h218 → _p2mH218
open _root_.P2M7374ab17 renaming h217 → _p2mH217
open _root_.P2M7374ab17 renaming h219 → _p2mH219
open _root_.P2M7374ab17 renaming h216 → _p2mH216
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
theorem _root_.P2M7374ab17.h101 (security order : ℕ)
    (first second : RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    interpret security order (RationalFamilyProductProgram.product order first second) =
      RationalFamilyProductProgram.product order (interpret security order first) (interpret security order second) := by
  unfold interpret
  rw [_p2mH214, _p2mH218]
open _root_.P2M7374ab17 renaming h101 → _p2mH101
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h100 (security order : ℕ) (first second : ActualFamily security order) :
    RationalFamilyProductProgram.product order (data security order first) (data security order second) =
      data security order (GradedControlAlgebra.familyProduct (ProposalPrimary.primaryLaw security)
        (ActualControls.bodyReference security) order first second) :=
  _p2mH212 _ _ _ _ _
open _root_.P2M7374ab17 renaming h100 → _p2mH100
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h102 (security order : ℕ) (family : ActualFamily security order) (bound : ℝ)
    (hbound : LocalRaisingBounds.coefficientNorm security order family ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |data security order family arity colors centers| ≤ coordinateFactor security order*bound := by
  exact (_p2mH35 security order family arity colors centers).trans
    (mul_le_mul_of_nonneg_left hbound (by positivity))
open _root_.P2M7374ab17 renaming h102 → _p2mH102
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h103 (order : ℕ) (A B e f : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hf : 0 ≤ f) :
    0 ≤ productError order A B e f := by
  unfold productError
  positivity
open _root_.P2M7374ab17 renaming h103 → _p2mH103
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h104 (security bits order : ℕ)
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
  rw [_p2mH101, ← _p2mH100]
  have h := _p2mH215 order
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
open _root_.P2M7374ab17 renaming h104 → _p2mH104
end
open _root_.P2M7374ab17 renaming h100 → _p2mH100
open _root_.P2M7374ab17 renaming h101 → _p2mH101
open _root_.P2M7374ab17 renaming h102 → _p2mH102
open _root_.P2M7374ab17 renaming h103 → _p2mH103
open _root_.P2M7374ab17 renaming h104 → _p2mH104
end CurrentAFT.RationalActualFamilyApproximation
open _root_.P2M7374ab17 renaming h100 → _p2mH100
open _root_.P2M7374ab17 renaming h101 → _p2mH101
open _root_.P2M7374ab17 renaming h102 → _p2mH102
open _root_.P2M7374ab17 renaming h103 → _p2mH103
open _root_.P2M7374ab17 renaming h104 → _p2mH104
end
open _root_.P2M7374ab17 renaming h104 → _p2mH104
open _root_.P2M7374ab17 renaming h103 → _p2mH103
open _root_.P2M7374ab17 renaming h100 → _p2mH100
open _root_.P2M7374ab17 renaming h102 → _p2mH102
open _root_.P2M7374ab17 renaming h101 → _p2mH101
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
theorem _root_.P2M7374ab17.h307 (security bits : ℕ) (primary output : FirstHistogram.Palette security) :
    |(anchor security bits primary.val output.val : ℝ) -
      (InwardAnchor.smoothedAnchorLaw security primary).weight output| ≤ 1 / (2 : ℝ)^bits := by
  rw [anchor_cast]
  have hl1 := _p2mH16 (WindowGaussianSampler.squaredWidth security)
    (Parameters.sourceWidth security) (Parameters.sourceCutoff security - 1) bits
    (_p2mH327 security) (_p2mH328 security).symm
  have h := _p2mH47
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits)
    (scalarLaw security)
    (fun scalar => (InwardAnchor.shiftedAnchorLaw security primary scalar.val
      (InwardAnchor.scalar_bound security scalar)).weight output) 1 (fun scalar => by
      rw [abs_of_nonneg ((InwardAnchor.shiftedAnchorLaw security primary scalar.val
        (InwardAnchor.scalar_bound security scalar)).nonneg output)]
      exact (InwardAnchor.shiftedAnchorLaw security primary scalar.val
        (InwardAnchor.scalar_bound security scalar)).atom_le_one output)
  exact h.trans (by simpa only [one_mul,scalarLaw] using hl1)
open _root_.P2M7374ab17 renaming h307 → _p2mH307
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h319 (security bits : ℕ) :
    (∑ seed, |(approximateSeedLaw security bits).weight seed - (actualSeedLaw security).weight seed|) ≤
      3 / (2 : ℝ)^bits := by
  have he := _p2mH16 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (edgeCutoff security) bits (_p2mH327 security)
    (_p2mH328 security).symm
  have hs := _p2mH16 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security - 1) bits (_p2mH327 security)
    (_p2mH328 security).symm
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
open _root_.P2M7374ab17 renaming h319 → _p2mH319
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h308 (security bits : ℕ) (includeScalar : Bool) (output : FirstHistogram.Palette security) :
    |(body security bits includeScalar output.val : ℝ) - (bodyLaw security includeScalar).weight output| ≤
      3 / (2 : ℝ)^bits := by
  rw [body_cast]
  exact (_p2mH47 (approximateSeedLaw security bits)
    (actualSeedLaw security) (fun seed => ((safeLaw security).map
      (shiftEquiv security (actualBlur security seed + if includeScalar then actualSecond security seed else 0))).weight output)
      1 (fun seed => by
        rw [abs_of_nonneg (FiniteDist.nonneg _ _)]
        exact FiniteDist.atom_le_one _ _)).trans (by simpa only [one_mul] using _p2mH319 security bits)
open _root_.P2M7374ab17 renaming h308 → _p2mH308
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h313 (colors width output : ℕ) (blur second : ℤ) :
    |(diffuseKernel colors width blur second output : ℝ)| ≤ 1 := by
  have hp := _p2mH25 colors 1
    ((width : ℤ) + blur) second width output
  have hm := _p2mH25 colors 1
    (-2 * (width : ℤ) + 1 + blur) second width output
  simp only [diffuseKernel, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (by linarith only [hp, hm])
open _root_.P2M7374ab17 renaming h313 → _p2mH313
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h314 (security bits : ℕ) (output : FirstHistogram.Palette security) :
    |(diffuse security bits output.val : ℝ) - diffuseMean security output| ≤ 3 / (2 : ℝ)^bits := by
  rw [diffuse_cast]
  change |fairProfile security (approximateSeedLaw security bits) output -
    fairProfile security (actualSeedLaw security) output| ≤ _
  rw [fairProfile_expectation, fairProfile_expectation]
  exact (_p2mH47 _ _ _ 1
    (fun seed => _p2mH313 _ _ _ _ _)).trans
      (by simpa only [one_mul] using _p2mH319 security bits)
open _root_.P2M7374ab17 renaming h314 → _p2mH314
set_option maxRecDepth 8192
private theorem _root_.P2M7374ab17.h335
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
open _root_.P2M7374ab17 renaming h335 → _p2mH335
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h316 (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ))) :
    |(primaryRaw security bits output.val : ℝ) - primaryProfile security output| ≤
      64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let rate : ℝ := LocalPairProgram.activationApprox security bits
  have hepsilon : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have hb := FirstResponse.base_pos security
  have hrate := LocalPairProgram.activationApprox_bounds security bits
  have hrateError : |rate - DiffuseProfiles.activation security| ≤ epsilon / 2 := by
    exact (_p2mH75 security bits).trans_eq (by dsimp only [epsilon]; ring)
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
    exact (_p2mH308 security bits false output).trans_eq (by dsimp only [epsilon]; ring)
  have honeError : |(bodyLaw security true).weight output - (approximateBodyLaw security bits true).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← body_cast]
    exact (_p2mH308 security bits true output).trans_eq (by dsimp only [epsilon]; ring)
  have hdiffuseError : |diffuseMean security output - (approximateDiffuseLaw security bits).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← diffuse_cast]
    exact (_p2mH314 security bits output).trans_eq (by dsimp only [epsilon]; ring)
  have hresidual := _p2mH335 (freeMass security) (Parameters.legCount security)
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
open _root_.P2M7374ab17 renaming h316 → _p2mH316
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h317 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : FirstHistogram.Palette security) :
    1 / (4 * (Parameters.modulus security : ℝ)) ≤ (primaryRaw security bits output.val : ℝ) := by
  have herr := (abs_le.mp (_p2mH316 security bits output hprecision)).1
  have hp := primaryProfile_atom_lower security output
  have hfrac : (1 : ℝ) / (2 * Parameters.modulus security) = 2 * (1 / (4 * Parameters.modulus security)) := by ring
  rw [hfrac] at hp
  linarith
open _root_.P2M7374ab17 renaming h317 → _p2mH317
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h315 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) : primaryGood security bits := by
  unfold primaryGood
  rw [PublicParameterProgram.modulus_value]
  intro output
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
    _p2mH317 security bits hprecision hbudget output
open _root_.P2M7374ab17 renaming h315 → _p2mH315
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h318 (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(primary security bits output.val : ℝ) - primaryProfile security output| ≤
      64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) := by
  rw [primary, if_pos (_p2mH315 security bits hprecision hbudget)]
  exact _p2mH316 security bits output hprecision
open _root_.P2M7374ab17 renaming h318 → _p2mH318
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h312 (security bits : ℕ) : (compensationApprox security bits : ℝ) ≤ 1 := by
  apply (compensationApprox_le_leg_body security bits).trans
  apply (div_le_one (bodySize_pos security)).mpr
  exact_mod_cast (show Parameters.legCount security ≤ Parameters.bodySize security by
    have := population_room security; omega)
open _root_.P2M7374ab17 renaming h312 → _p2mH312
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h310 (security bits : ℕ) (output : ActualControls.SafePalette security) :
    1 / (2 * (Parameters.modulus security : ℝ)) ≤ (center security bits output.val.val : ℝ) := by
  rw [center_cast]
  apply le_trans _ (approximateCenterProfile_bounds security bits output.val).1
  rw [safeLaw_weight, if_pos output.property]
  have hsafe : 1 / (Parameters.modulus security : ℝ) ≤ safeHeight security := by
    unfold safeHeight
    apply one_div_le_one_div_of_le
    · have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
      push_cast at h
      linarith
    · have hM : (0 : ℝ) ≤ Parameters.safeMargin security := Nat.cast_nonneg _
      linarith
  convert div_le_div_of_nonneg_right hsafe (by norm_num : (0 : ℝ) ≤ 2) using 1; ring
open _root_.P2M7374ab17 renaming h310 → _p2mH310
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h311 (security bits : ℕ) :
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
      mul_le_mul_of_nonneg_left (_p2mH75 security bits)
        (div_nonneg (Nat.cast_nonneg _) hfree.le)
    _ ≤ 1 * ((1 / 2 : ℝ) * (1 / (2 : ℝ)^bits)) := mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by ring
open _root_.P2M7374ab17 renaming h311 → _p2mH311
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h306 (security bits : ℕ) (output : FirstHistogram.Palette security)
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
      _p2mH318 security bits color hprecision hbudget
    have hk : |(approximateAnchorLaw security bits color).weight output -
        (InwardAnchor.smoothedAnchorLaw security color).weight output| ≤ epsilon := by
      rw [← anchor_cast]
      exact _p2mH307 security bits color output
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
open _root_.P2M7374ab17 renaming h306 → _p2mH306
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h309 (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(center security bits output.val : ℝ) - centerProfile security output| ≤
      (64 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security + 2) *
        (1 / (2 : ℝ)^bits) := by
  have hcomp := _p2mH311 security bits
  have hanchor := _p2mH306 security bits output hprecision hbudget
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
        (mul_le_mul (_p2mH312 security bits) hanchor (abs_nonneg _) (by positivity))
    _ = _ := by ring
open _root_.P2M7374ab17 renaming h309 → _p2mH309
end
open _root_.P2M7374ab17 renaming h306 → _p2mH306
open _root_.P2M7374ab17 renaming h307 → _p2mH307
open _root_.P2M7374ab17 renaming h308 → _p2mH308
open _root_.P2M7374ab17 renaming h309 → _p2mH309
open _root_.P2M7374ab17 renaming h310 → _p2mH310
open _root_.P2M7374ab17 renaming h311 → _p2mH311
open _root_.P2M7374ab17 renaming h312 → _p2mH312
open _root_.P2M7374ab17 renaming h313 → _p2mH313
open _root_.P2M7374ab17 renaming h314 → _p2mH314
open _root_.P2M7374ab17 renaming h315 → _p2mH315
open _root_.P2M7374ab17 renaming h316 → _p2mH316
open _root_.P2M7374ab17 renaming h317 → _p2mH317
open _root_.P2M7374ab17 renaming h318 → _p2mH318
open _root_.P2M7374ab17 renaming h319 → _p2mH319
open _root_.P2M7374ab17 renaming h335 → _p2mH335
end CurrentAFT.RationalProposalProgram
open _root_.P2M7374ab17 renaming h306 → _p2mH306
open _root_.P2M7374ab17 renaming h307 → _p2mH307
open _root_.P2M7374ab17 renaming h308 → _p2mH308
open _root_.P2M7374ab17 renaming h309 → _p2mH309
open _root_.P2M7374ab17 renaming h310 → _p2mH310
open _root_.P2M7374ab17 renaming h311 → _p2mH311
open _root_.P2M7374ab17 renaming h312 → _p2mH312
open _root_.P2M7374ab17 renaming h313 → _p2mH313
open _root_.P2M7374ab17 renaming h314 → _p2mH314
open _root_.P2M7374ab17 renaming h315 → _p2mH315
open _root_.P2M7374ab17 renaming h316 → _p2mH316
open _root_.P2M7374ab17 renaming h317 → _p2mH317
open _root_.P2M7374ab17 renaming h318 → _p2mH318
open _root_.P2M7374ab17 renaming h319 → _p2mH319
open _root_.P2M7374ab17 renaming h335 → _p2mH335
end
open _root_.P2M7374ab17 renaming h308 → _p2mH308
open _root_.P2M7374ab17 renaming h312 → _p2mH312
open _root_.P2M7374ab17 renaming h314 → _p2mH314
open _root_.P2M7374ab17 renaming h316 → _p2mH316
open _root_.P2M7374ab17 renaming h318 → _p2mH318
open _root_.P2M7374ab17 renaming h319 → _p2mH319
open _root_.P2M7374ab17 renaming h311 → _p2mH311
open _root_.P2M7374ab17 renaming h307 → _p2mH307
open _root_.P2M7374ab17 renaming h313 → _p2mH313
open _root_.P2M7374ab17 renaming h317 → _p2mH317
open _root_.P2M7374ab17 renaming h315 → _p2mH315
open _root_.P2M7374ab17 renaming h309 → _p2mH309
open _root_.P2M7374ab17 renaming h310 → _p2mH310
open _root_.P2M7374ab17 renaming h306 → _p2mH306
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
theorem _root_.P2M7374ab17.h138 (security : ℕ) : margin security = Parameters.safeMargin security := by
  simp only [margin, Parameters.safeMargin, Parameters.sourceCutoff, Parameters.base]
open _root_.P2M7374ab17 renaming h138 → _p2mH138
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h141 (security : ℕ) (output : FirstHistogram.Palette security) :
    (safe security output.val:ℝ) = (safeLaw security).weight output := by
  unfold safe RationalProposalProgram.safeEntry
  rw [colors, PublicParameterProgram.modulus_value, _p2mH138, AFT.V7Calibration.sliceProbabilityProgram_cast]
  rw [safeLaw, TrimmedSlice.finiteLaw_weight]
open _root_.P2M7374ab17 renaming h141 → _p2mH141
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h144 (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    (shifted security shift output.val:ℝ) = (shiftedSafeLaw security shift).weight output := by
  unfold shifted
  rw [colors, PublicParameterProgram.modulus_value, _p2mH138]
  exact RationalProposalProgram.bodyKernel_cast security shift output
open _root_.P2M7374ab17 renaming h144 → _p2mH144
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h142 (security : ℕ) (output : FirstHistogram.Palette security) :
    Safe security output.val ↔ InwardAnchor.SafeColor security output := by
  unfold Safe InwardAnchor.SafeColor
  rw [colors, PublicParameterProgram.modulus_value, _p2mH138]
open _root_.P2M7374ab17 renaming h142 → _p2mH142
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h146 (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    (unsafeProfile security shift output.val:ℝ) = BackgroundTranslations.unsafePart security shift output := by
  unfold unsafeProfile BackgroundTranslations.unsafePart
  by_cases h : InwardAnchor.SafeColor security output
  · rw [if_pos ((_p2mH142 security output).mpr h), if_pos h]
    exact Rat.cast_zero
  · rw [if_neg (fun hs => h ((_p2mH142 security output).mp hs)), if_neg h]
    exact _p2mH144 security shift output
open _root_.P2M7374ab17 renaming h146 → _p2mH146
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h145 (security : ℕ) (shift : ℤ) :
    (unsafeTotal security shift:ℝ) = BackgroundTranslations.unsafeMass security shift := by
  unfold unsafeTotal BackgroundTranslations.unsafeMass
  rw [Rat.cast_sum]
  have he : colors security = Parameters.modulus security := PublicParameterProgram.modulus_value security
  rw [he]
  apply Finset.sum_congr (by ext; simp)
  intro output _
  exact _p2mH146 security shift output
open _root_.P2M7374ab17 renaming h145 → _p2mH145
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h139 (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    (projected security shift output.val:ℝ) = BackgroundTranslations.projectedShiftProfile security shift output := by
  simp only [projected, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, _p2mH144, _p2mH146,
    _p2mH145, _p2mH141, BackgroundTranslations.projectedShiftProfile]
open _root_.P2M7374ab17 renaming h139 → _p2mH139
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h143 (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    (seedProfile security shift output.val:ℝ) = BackgroundTranslations.safeSeedProfile security shift output := by
  simp only [seedProfile, Rat.cast_sub, _p2mH139, _p2mH141, BackgroundTranslations.safeSeedProfile]
open _root_.P2M7374ab17 renaming h143 → _p2mH143
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h137 (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    inverseShift security shift output.val = ((shiftEquiv security shift).symm output).val := by
  rw [_p2mH98]
  have h := (RationalProposalProgram.shift_condition security (-shift) output (shiftEquiv security (-shift) output)).mp rfl
  have hh := congrArg Int.toNat h
  simpa only [inverseShift, colors, PublicParameterProgram.modulus_value, sub_eq_add_neg, Int.toNat_natCast] using hh
open _root_.P2M7374ab17 renaming h137 → _p2mH137
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h134 (security bits : ℕ) (profile : ℕ → ℚ) (output : FirstHistogram.Palette security) :
    (convolution security bits profile output.val:ℝ) =
      (RationalProposalProgram.approximateSeedLaw security bits).expectation (fun seed =>
        (profile ((shiftEquiv security (actualBlur security seed)).symm output).val:ℝ)) := by
  rw [convolution, RationalProposalProgram.seedEvaluate_cast]
  apply congrArg (FiniteDist.expectation (RationalProposalProgram.approximateSeedLaw security bits))
  funext seed
  rw [_p2mH137]
  rfl
open _root_.P2M7374ab17 renaming h134 → _p2mH134
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h135 (security bits : ℕ) (profile : ℕ → ℚ) (ideal : FirstHistogram.Palette security → ℝ)
    (hprofile : ∀ output, (profile output.val:ℝ) = ideal output) (bound : ℝ)
    (hbound : ∀ output, |ideal output| ≤ bound) (output : FirstHistogram.Palette security) :
    |(convolution security bits profile output.val:ℝ)-rootConvolutionProfile security ideal output| ≤
      bound*(3/(2:ℝ)^bits) := by
  rw [_p2mH134]
  simp_rw [hprofile]
  exact (_p2mH47 (RationalProposalProgram.approximateSeedLaw security bits)
    (actualSeedLaw security) (fun seed => ideal ((shiftEquiv security (actualBlur security seed)).symm output)) bound
    (fun seed => hbound _)).trans
    (mul_le_mul_of_nonneg_left (_p2mH319 security bits)
      ((abs_nonneg (ideal output)).trans (hbound output)))
open _root_.P2M7374ab17 renaming h135 → _p2mH135
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h136 (security bits : ℕ) (profile : ℕ → ℚ) (ideal : FirstHistogram.Palette security → ℝ)
    (bound profileError : ℝ) (hbound : ∀ output : FirstHistogram.Palette security, |(profile output.val:ℝ)| ≤ bound)
    (hdiff : ∀ output : FirstHistogram.Palette security, |(profile output.val:ℝ)-ideal output| ≤ profileError)
    (output : FirstHistogram.Palette security) :
    |(convolution security bits profile output.val:ℝ)-rootConvolutionProfile security ideal output| ≤
      bound*(3/(2:ℝ)^bits)+profileError := by
  have hfirst := _p2mH135 security bits profile (fun color => (profile color.val:ℝ))
    (fun _ => rfl) bound hbound output
  have hsecond := _p2mH42 (actualSeedLaw security)
    (fun seed => (profile ((shiftEquiv security (actualBlur security seed)).symm output).val:ℝ)-
      ideal ((shiftEquiv security (actualBlur security seed)).symm output)) profileError (fun seed => hdiff _)
  have hs : |rootConvolutionProfile security (fun color => (profile color.val:ℝ)) output-
      rootConvolutionProfile security ideal output| ≤ profileError := by
    simpa only [rootConvolutionProfile, FiniteDist.expectation, mul_sub, Finset.sum_sub_distrib] using hsecond
  exact (abs_sub_le _ (rootConvolutionProfile security (fun color => (profile color.val:ℝ)) output) _).trans
    (add_le_add hfirst hs)
open _root_.P2M7374ab17 renaming h136 → _p2mH136
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h133 (security bits : ℕ) (output : FirstHistogram.Palette security) :
    |(bodyDeviation security bits output.val:ℝ)-FringeCertificate.bodyDeviation security output| ≤ 3/(2:ℝ)^bits := by
  simp only [bodyDeviation, colors, Rat.cast_sub, one_div, Rat.cast_inv, Rat.cast_natCast,
    PublicParameterProgram.modulus_value, FringeCertificate.bodyDeviation, FringeCertificate.uniformProfile]
  convert _p2mH308 security bits false output using 1
  congr 1
  ring
open _root_.P2M7374ab17 renaming h133 → _p2mH133
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h140 (security bits : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    |(residual security bits shift output.val:ℝ)-BackgroundTranslations.translationResidual security shift output| ≤ 6/(2:ℝ)^bits := by
  have hu (color : FirstHistogram.Palette security) : |BackgroundTranslations.unsafePart security shift color| ≤ 1 := by
    rw [abs_of_nonneg (BackgroundTranslations.unsafePart_nonneg security shift color)]
    exact (BackgroundTranslations.unsafePart_le_shifted security shift color).trans ((shiftedSafeLaw security shift).atom_le_one color)
  have hc := _p2mH135 security bits (unsafeProfile security shift) (BackgroundTranslations.unsafePart security shift)
    (_p2mH146 security shift) 1 hu output
  have hm := BackgroundTranslations.unsafeMass_le_one security shift
  have hn := BackgroundTranslations.unsafeMass_nonneg security shift
  have hb := _p2mH308 security bits false output
  simp only [residual, Rat.cast_sub, Rat.cast_mul, _p2mH145, BackgroundTranslations.translationResidual]
  have hsplit : (convolution security bits (unsafeProfile security shift) output.val:ℝ)-
      BackgroundTranslations.unsafeMass security shift*(RationalProposalProgram.body security bits false output.val:ℝ)-
      (rootConvolutionProfile security (BackgroundTranslations.unsafePart security shift) output-
        BackgroundTranslations.unsafeMass security shift*(bodyLaw security false).weight output) =
    ((convolution security bits (unsafeProfile security shift) output.val:ℝ)-rootConvolutionProfile security (BackgroundTranslations.unsafePart security shift) output)-
      BackgroundTranslations.unsafeMass security shift*((RationalProposalProgram.body security bits false output.val:ℝ)-(bodyLaw security false).weight output) := by ring
  rw [hsplit]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg hn]
  exact (add_le_add hc (mul_le_mul hm hb (abs_nonneg _) (by norm_num))).trans_eq (by ring)
open _root_.P2M7374ab17 renaming h140 → _p2mH140
end
open _root_.P2M7374ab17 renaming h133 → _p2mH133
open _root_.P2M7374ab17 renaming h134 → _p2mH134
open _root_.P2M7374ab17 renaming h135 → _p2mH135
open _root_.P2M7374ab17 renaming h136 → _p2mH136
open _root_.P2M7374ab17 renaming h137 → _p2mH137
open _root_.P2M7374ab17 renaming h138 → _p2mH138
open _root_.P2M7374ab17 renaming h139 → _p2mH139
open _root_.P2M7374ab17 renaming h140 → _p2mH140
open _root_.P2M7374ab17 renaming h141 → _p2mH141
open _root_.P2M7374ab17 renaming h142 → _p2mH142
open _root_.P2M7374ab17 renaming h143 → _p2mH143
open _root_.P2M7374ab17 renaming h144 → _p2mH144
open _root_.P2M7374ab17 renaming h145 → _p2mH145
open _root_.P2M7374ab17 renaming h146 → _p2mH146
end CurrentAFT.RationalBackgroundProfiles
open _root_.P2M7374ab17 renaming h133 → _p2mH133
open _root_.P2M7374ab17 renaming h134 → _p2mH134
open _root_.P2M7374ab17 renaming h135 → _p2mH135
open _root_.P2M7374ab17 renaming h136 → _p2mH136
open _root_.P2M7374ab17 renaming h137 → _p2mH137
open _root_.P2M7374ab17 renaming h138 → _p2mH138
open _root_.P2M7374ab17 renaming h139 → _p2mH139
open _root_.P2M7374ab17 renaming h140 → _p2mH140
open _root_.P2M7374ab17 renaming h141 → _p2mH141
open _root_.P2M7374ab17 renaming h142 → _p2mH142
open _root_.P2M7374ab17 renaming h143 → _p2mH143
open _root_.P2M7374ab17 renaming h144 → _p2mH144
open _root_.P2M7374ab17 renaming h145 → _p2mH145
open _root_.P2M7374ab17 renaming h146 → _p2mH146
end
open _root_.P2M7374ab17 renaming h135 → _p2mH135
open _root_.P2M7374ab17 renaming h134 → _p2mH134
open _root_.P2M7374ab17 renaming h133 → _p2mH133
open _root_.P2M7374ab17 renaming h138 → _p2mH138
open _root_.P2M7374ab17 renaming h142 → _p2mH142
open _root_.P2M7374ab17 renaming h145 → _p2mH145
open _root_.P2M7374ab17 renaming h144 → _p2mH144
open _root_.P2M7374ab17 renaming h139 → _p2mH139
open _root_.P2M7374ab17 renaming h137 → _p2mH137
open _root_.P2M7374ab17 renaming h136 → _p2mH136
open _root_.P2M7374ab17 renaming h141 → _p2mH141
open _root_.P2M7374ab17 renaming h140 → _p2mH140
open _root_.P2M7374ab17 renaming h146 → _p2mH146
open _root_.P2M7374ab17 renaming h143 → _p2mH143
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
theorem _root_.P2M7374ab17.h234 (colors width output : ℕ) (positive : Bool) (blur source : ℤ) :
    |(profileKernel colors width positive blur source output : ℝ)| ≤ 1 :=
  _p2mH25 _ _ _ _ _ _
open _root_.P2M7374ab17 renaming h234 → _p2mH234
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h236 (security : ℕ) (positive : Bool) (output : FirstHistogram.Palette security) :
    (actualSeedLaw security).expectation (fun seed =>
      (profileKernel (Parameters.modulus security) (Parameters.anchorWidth security) positive
        (actualBlur security seed) (actualSecond security seed) output.val : ℝ)) = actualProfile security positive output := by
  simp only [profileKernel, AFT.V7Calibration.averagedSliceProgram_cast, actualProfile, DiffuseProfiles.profile,
    TrimmedSlice.mixedLaw, FiniteDist.expectation, intervalStart]
open _root_.P2M7374ab17 renaming h236 → _p2mH236
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h235 (security bits : ℕ) (positive : Bool) (output : FirstHistogram.Palette security) :
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
      congrArg abs (congrArg₂ (·-·) he (_p2mH236 security positive output).symm)
    _ ≤ _ := (_p2mH47 _ _ _ 1
      (fun seed => _p2mH234 _ _ _ _ _ _)).trans (by simpa only [one_mul] using _p2mH319 security bits)
open _root_.P2M7374ab17 renaming h235 → _p2mH235
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h225 (security : ℕ) (positive : Bool) (output : FirstHistogram.Palette security) :
    |actualProfile security positive output| ≤ 1 := by
  rw [← _p2mH236]
  unfold FiniteDist.expectation
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ seed : ActualSeed security, (actualSeedLaw security).weight seed := by
      apply Finset.sum_le_sum
      intro seed _
      rw [abs_mul, abs_of_nonneg ((actualSeedLaw security).nonneg seed)]
      exact (mul_le_mul_of_nonneg_left (_p2mH234 _ _ _ _ _ _)
        ((actualSeedLaw security).nonneg seed)).trans_eq (mul_one _)
    _ = 1 := (actualSeedLaw security).sum_one
open _root_.P2M7374ab17 renaming h225 → _p2mH225
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h237 (security bits : ℕ) (output : FirstHistogram.Palette security) :
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
  have he := _p2mH75 security bits
  have hp : |first-trueFirst| ≤ 3/(2:ℝ)^bits := _p2mH235 security bits true output
  have hm : |second-trueSecond| ≤ 3/(2:ℝ)^bits := _p2mH235 security bits false output
  have hd : |(first-trueFirst)-(second-trueSecond)| ≤ 6/(2:ℝ)^bits :=
    (abs_sub _ _).trans ((add_le_add hp hm).trans_eq (by ring))
  have hg : |trueFirst-trueSecond| ≤ 2 :=
    (abs_sub _ _).trans (by linarith only [_p2mH225 security true output, _p2mH225 security false output])
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
open _root_.P2M7374ab17 renaming h237 → _p2mH237
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h227 (security : ℕ) (color : FirstHistogram.Palette security) :
    (anchorSign security color.val : ℝ) = FirstResponse.anchorSign security color := by
  unfold anchorSign FirstResponse.anchorSign
  rw [PublicParameterProgram.modulus_value]
  split_ifs <;> norm_num
open _root_.P2M7374ab17 renaming h227 → _p2mH227
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h231 (security : ℕ) (input : ℕ → ℚ) :
    (functional security input : ℝ) =
      AFT.signFunctional (FirstResponse.anchorSign security) (fun color : FirstHistogram.Palette security => (input color.val : ℝ)) := by
  simp only [functional, Rat.cast_sum, Rat.cast_mul]
  rw [PublicParameterProgram.modulus_value]
  simp only [_p2mH227, AFT.signFunctional]
open _root_.P2M7374ab17 renaming h231 → _p2mH231
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h228 (security bits : ℕ) :
    |(denominator security bits : ℝ)-actualDenominator security| ≤
      (8*(Parameters.modulus security:ℝ)+1)/(2:ℝ)^bits := by
  have ha := _p2mH75 security bits
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
          (_p2mH237 security bits color) (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
      _ = _ := by simp
  unfold denominator actualDenominator
  rw [Rat.cast_add, _p2mH231]
  calc
    _ = |((LocalPairProgram.activationApprox security bits : ℝ)-DiffuseProfiles.activation security) +
        (AFT.signFunctional (FirstResponse.anchorSign security) (fun color => (signProfile security bits color.val : ℝ))-
          AFT.signFunctional (FirstResponse.anchorSign security) (DiffuseProfiles.signProfile security))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add ha hs)
    _ = ((1/2:ℝ)+7*Parameters.modulus security)/(2:ℝ)^bits := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by have hq := FirstResponse.modulus_pos security; linarith) (by positivity)
open _root_.P2M7374ab17 renaming h228 → _p2mH228
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h229 (security bits : ℕ) (hprecision : PrecisionBudget security bits) :
    1/(16*(Parameters.base security:ℝ)) ≤ (denominator security bits : ℝ) := by
  have hb := FirstResponse.base_pos security
  have ha := FirstResponse.activation_lower_simple security
  have hd := _p2mH55 security
  change DiffuseProfiles.activation security/2 ≤ actualDenominator security at hd
  have he := _p2mH228 security bits
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
open _root_.P2M7374ab17 renaming h229 → _p2mH229
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h232 (security bits : ℕ) (hprecision : PrecisionBudget security bits) :
    guardedDenominator security bits = denominator security bits := by
  have hd := _p2mH55 security
  change DiffuseProfiles.activation security/2 ≤ actualDenominator security at hd
  have ha := FirstResponse.activation_lower_simple security
  have hal : 1/(16*(Parameters.base security:ℝ)) ≤ DiffuseProfiles.activation security/4 := by
    convert div_le_div_of_nonneg_right ha (by norm_num : (0:ℝ) ≤ 4) using 1 <;> first | rfl | ring
  have he := _p2mH228 security bits
  have he' : |(denominator security bits : ℝ)-actualDenominator security| ≤
      (8*(Parameters.modulus security:ℝ)+1)*(1/(2:ℝ)^bits) := he.trans_eq (by ring)
  have hae := _p2mH75 security bits
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
open _root_.P2M7374ab17 renaming h232 → _p2mH232
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h224 (security : ℕ) :
    1/(16*(Parameters.base security:ℝ)) ≤ actualDenominator security := by
  have ha := FirstResponse.activation_lower_simple security
  have hd := _p2mH55 security
  change DiffuseProfiles.activation security/2 ≤ actualDenominator security at hd
  have hal : 1/(8*(Parameters.base security:ℝ)) ≤ DiffuseProfiles.activation security/2 := by
    convert div_le_div_of_nonneg_right ha (by norm_num : (0:ℝ) ≤ 2) using 1 <;> first | rfl | ring
  apply le_trans _ (hal.trans hd)
  exact one_div_le_one_div_of_le (by have hb := FirstResponse.base_pos security; positivity) (by
    have hb := FirstResponse.base_pos security; nlinarith)
open _root_.P2M7374ab17 renaming h224 → _p2mH224
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h230 (security : ℕ) (input : ℕ → ℚ) (bound : ℝ) (_hbound : 0 ≤ bound)
    (hinput : ∀ color : FirstHistogram.Palette security, |(input color.val : ℝ)| ≤ bound) :
    |(functional security input : ℝ)| ≤ (Parameters.modulus security:ℝ)*bound := by
  rw [_p2mH231]
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
open _root_.P2M7374ab17 renaming h230 → _p2mH230
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h226 (security : ℕ) (color : FirstHistogram.Palette security) :
    |DiffuseProfiles.signProfile security color| ≤ 2 := by
  have ha := DiffuseProfiles.activation_pos security
  have hu := DiffuseProfiles.activation_le_half security
  unfold DiffuseProfiles.signProfile
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-DiffuseProfiles.activation security)]
  have hgap : |actualProfile security true color - actualProfile security false color| ≤ 2 :=
    (abs_sub _ _).trans ((add_le_add (_p2mH225 security true color)
      (_p2mH225 security false color)).trans_eq (by norm_num))
  exact (mul_le_mul (by linarith : 1-DiffuseProfiles.activation security ≤ 1)
    hgap (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (by norm_num)
open _root_.P2M7374ab17 renaming h226 → _p2mH226
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h233 (security bits : ℕ) (input : ℕ → ℚ) (output : FirstHistogram.Palette security)
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
  have ha : 1/(16*base) ≤ a := _p2mH229 security bits hprecision
  have hd : 1/(16*base) ≤ d := _p2mH224 security
  have ha0 : 0 < a := hlo.trans_le ha
  have hd0 : 0 < d := hlo.trans_le hd
  have hai : a⁻¹ ≤ 16*base := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le hlo ha
  have hdi : d⁻¹ ≤ 16*base := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le hlo hd
  have he : |a-d| ≤ (8*(Parameters.modulus security:ℝ)+1)*epsilon :=
    (_p2mH228 security bits).trans_eq (by dsimp only [epsilon]; ring)
  have hr : |r| ≤ 2 := _p2mH226 security output
  have hs : |s-r| ≤ 7*epsilon := (_p2mH237 security bits output).trans_eq (by dsimp only [epsilon]; ring)
  have hf : |f| ≤ (Parameters.modulus security:ℝ)*bound := _p2mH230 security input bound hbound hinput
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
    rw [_p2mH56]
    simp only [inverse, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, _p2mH232 security bits hprecision,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← _p2mH231]
    change (input output.val:ℝ)-f/a*s - ((input output.val:ℝ)-d⁻¹*f*r) = _
    ring
  rw [hformula, abs_mul, abs_neg]
  calc
    _ ≤ ((Parameters.modulus security:ℝ)*bound)*(7*epsilon*(16*base) +
        2*(256*base^2*((8*(Parameters.modulus security:ℝ)+1)*epsilon))) :=
      mul_le_mul hf hratio (abs_nonneg _) (by have hq := FirstResponse.modulus_pos security; positivity)
    _ = _ := by unfold inverseErrorConstant; dsimp only [base, epsilon]; ring
open _root_.P2M7374ab17 renaming h233 → _p2mH233
attribute [local irreducible] sufficientBits
end
open _root_.P2M7374ab17 renaming h224 → _p2mH224
open _root_.P2M7374ab17 renaming h225 → _p2mH225
open _root_.P2M7374ab17 renaming h226 → _p2mH226
open _root_.P2M7374ab17 renaming h227 → _p2mH227
open _root_.P2M7374ab17 renaming h228 → _p2mH228
open _root_.P2M7374ab17 renaming h229 → _p2mH229
open _root_.P2M7374ab17 renaming h230 → _p2mH230
open _root_.P2M7374ab17 renaming h231 → _p2mH231
open _root_.P2M7374ab17 renaming h232 → _p2mH232
open _root_.P2M7374ab17 renaming h233 → _p2mH233
open _root_.P2M7374ab17 renaming h234 → _p2mH234
open _root_.P2M7374ab17 renaming h235 → _p2mH235
open _root_.P2M7374ab17 renaming h236 → _p2mH236
open _root_.P2M7374ab17 renaming h237 → _p2mH237
end CurrentAFT.RationalFirstResponseProgram
open _root_.P2M7374ab17 renaming h224 → _p2mH224
open _root_.P2M7374ab17 renaming h225 → _p2mH225
open _root_.P2M7374ab17 renaming h226 → _p2mH226
open _root_.P2M7374ab17 renaming h227 → _p2mH227
open _root_.P2M7374ab17 renaming h228 → _p2mH228
open _root_.P2M7374ab17 renaming h229 → _p2mH229
open _root_.P2M7374ab17 renaming h230 → _p2mH230
open _root_.P2M7374ab17 renaming h231 → _p2mH231
open _root_.P2M7374ab17 renaming h232 → _p2mH232
open _root_.P2M7374ab17 renaming h233 → _p2mH233
open _root_.P2M7374ab17 renaming h234 → _p2mH234
open _root_.P2M7374ab17 renaming h235 → _p2mH235
open _root_.P2M7374ab17 renaming h236 → _p2mH236
open _root_.P2M7374ab17 renaming h237 → _p2mH237
end
open _root_.P2M7374ab17 renaming h233 → _p2mH233
open _root_.P2M7374ab17 renaming h227 → _p2mH227
open _root_.P2M7374ab17 renaming h225 → _p2mH225
open _root_.P2M7374ab17 renaming h224 → _p2mH224
open _root_.P2M7374ab17 renaming h236 → _p2mH236
open _root_.P2M7374ab17 renaming h230 → _p2mH230
open _root_.P2M7374ab17 renaming h237 → _p2mH237
open _root_.P2M7374ab17 renaming h235 → _p2mH235
open _root_.P2M7374ab17 renaming h234 → _p2mH234
open _root_.P2M7374ab17 renaming h229 → _p2mH229
open _root_.P2M7374ab17 renaming h232 → _p2mH232
open _root_.P2M7374ab17 renaming h231 → _p2mH231
open _root_.P2M7374ab17 renaming h226 → _p2mH226
open _root_.P2M7374ab17 renaming h228 → _p2mH228
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
theorem _root_.P2M7374ab17.h165 (security : ℕ) (profile : FirstHistogram.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hprofile : ∀ color, |profile color| ≤ bound)
    (output : FirstHistogram.Palette security) :
    |(FirstResponse.responseEquiv security).symm profile output| ≤ inverseBound security*bound := by
  have hfunctional : |signFunctional (FirstResponse.anchorSign security) profile| ≤
      (Parameters.modulus security:ℝ)*bound := by
    apply (signFunctional_abs_le_l1 _ _ (FirstResponse.anchorSign_abs_le_one security)).trans
    calc
      _ ≤ ∑ _color : FirstHistogram.Palette security, bound := Finset.sum_le_sum (fun color _ => hprofile color)
      _ = _ := by simp
  have hlo := _p2mH224 security
  have hb0 := FirstResponse.base_pos security
  have hpos : 0 < RationalFirstResponseProgram.actualDenominator security :=
    (by positivity : (0:ℝ)<1/(16*(Parameters.base security:ℝ))).trans_le hlo
  have hinv : (RationalFirstResponseProgram.actualDenominator security)⁻¹ ≤ 16*(Parameters.base security:ℝ) := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le
      (by positivity : (0:ℝ)<1/(16*(Parameters.base security:ℝ))) hlo
  rw [_p2mH56]
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
          (_p2mH226 security output) (abs_nonneg _) (by positivity))
    _ = _ := by unfold inverseBound; ring
open _root_.P2M7374ab17 renaming h165 → _p2mH165
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h167 (u v a b lower numeratorError denominatorError bound : ℝ)
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
open _root_.P2M7374ab17 renaming h167 → _p2mH167
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h164 (security bits : ℕ)
    (hprecision : RationalFirstResponseProgram.PrecisionBudget security bits) :
    1/(8*(Parameters.base security:ℝ)) ≤ (LocalPairProgram.activationApprox security bits:ℝ) := by
  have ha := FirstResponse.activation_lower_simple security
  have he := _p2mH75 security bits
  have hp : (8*(Parameters.modulus security:ℝ)+2)*(1/(2:ℝ)^bits) ≤
      1/(16*(Parameters.base security:ℝ)) := hprecision
  have hq := FirstResponse.modulus_pos security
  have hl := (abs_le.mp he).1
  have h0 : 0 ≤ 1/(2:ℝ)^bits := by positivity
  have hscale : 1/(4*(Parameters.base security:ℝ)) = 4*(1/(16*(Parameters.base security:ℝ))) := by ring
  have hscale' : 1/(8*(Parameters.base security:ℝ)) = 2*(1/(16*(Parameters.base security:ℝ))) := by ring
  nlinarith only [ha, hp, hq, hl, h0, hscale, hscale']
open _root_.P2M7374ab17 renaming h164 → _p2mH164
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h166 (security bits : ℕ) (score : ℕ → ℚ) (output : FirstHistogram.Palette security)
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
    simpa only [ProposalPrimary.primaryLaw] using _p2mH318 security bits color hprecision hbudget
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
    (_p2mH233 security bits approximate output bound hb haProfile hfirst).trans_eq (by dsimp only [epsilon]; ring)
  have hn2 : |middle-realNumerator| ≤ inverseBound security*(coefficient*epsilon*bound) := by
    have h := _p2mH165 security (approximateProfile-realProfile) (coefficient*epsilon*bound)
      (by positivity) hdProfile output
    simpa only [map_sub, Pi.sub_apply] using h
  have hn : |approximateNumerator-realNumerator| ≤
      (RationalFirstResponseProgram.inverseErrorConstant security+inverseBound security*coefficient)*bound*epsilon :=
    (abs_sub_le _ middle _).trans ((add_le_add hn1 hn2).trans_eq (by ring))
  have hnum : |realNumerator| ≤ inverseBound security*bound := _p2mH165 security realProfile bound hb hrProfile output
  have hpa := primary_lower security bits output
  have hpr : 1/(2*q) ≤ (ProposalPrimary.primaryLaw security).weight output := by
    simpa only [ProposalPrimary.primaryLaw] using ProposalPrimary.primaryProfile_atom_lower security output
  have haa := _p2mH164 security bits hfirst
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
    have herr := _p2mH75 security bits
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
  have hquot := _p2mH167 approximateNumerator realNumerator a b lower
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
open _root_.P2M7374ab17 renaming h166 → _p2mH166
end
open _root_.P2M7374ab17 renaming h164 → _p2mH164
open _root_.P2M7374ab17 renaming h165 → _p2mH165
open _root_.P2M7374ab17 renaming h166 → _p2mH166
open _root_.P2M7374ab17 renaming h167 → _p2mH167
end CurrentAFT.RationalDensityInverseProgram
open _root_.P2M7374ab17 renaming h164 → _p2mH164
open _root_.P2M7374ab17 renaming h165 → _p2mH165
open _root_.P2M7374ab17 renaming h166 → _p2mH166
open _root_.P2M7374ab17 renaming h167 → _p2mH167
end
open _root_.P2M7374ab17 renaming h167 → _p2mH167
open _root_.P2M7374ab17 renaming h164 → _p2mH164
open _root_.P2M7374ab17 renaming h166 → _p2mH166
open _root_.P2M7374ab17 renaming h165 → _p2mH165
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
theorem _root_.P2M7374ab17.h324 (security : ℕ) : 0 ≤ actualBound security := by
  unfold actualBound RationalDensityInverseProgram.inverseBound
  positivity
open _root_.P2M7374ab17 renaming h324 → _p2mH324
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h325 (security : ℕ) (input : Palette security → ℝ) (bound : ℝ)
    (hb : 0 ≤ bound) (hinput : ∀ color, |input color| ≤ bound) (output : Palette security) :
    |PrimaryTensorInverse.densityInverse security input output| ≤ actualBound security * bound := by
  let profile := fun color : Palette security => (primaryLaw security).weight color * input color
  have hprofile (color : Palette security) : |profile color| ≤ bound := by
    dsimp only [profile]
    rw [abs_mul, abs_of_nonneg ((primaryLaw security).nonneg color)]
    exact (mul_le_mul ((primaryLaw security).atom_le_one color) (hinput color) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hnum := _p2mH165 security profile bound hb hprofile output
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
open _root_.P2M7374ab17 renaming h325 → _p2mH325
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h326 {Index : Type*} [DecidableEq Index]
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
open _root_.P2M7374ab17 renaming h326 → _p2mH326
end
open _root_.P2M7374ab17 renaming h324 → _p2mH324
open _root_.P2M7374ab17 renaming h325 → _p2mH325
open _root_.P2M7374ab17 renaming h326 → _p2mH326
end CurrentAFT.RationalTensorInverseProgram
open _root_.P2M7374ab17 renaming h324 → _p2mH324
open _root_.P2M7374ab17 renaming h325 → _p2mH325
open _root_.P2M7374ab17 renaming h326 → _p2mH326
end
open _root_.P2M7374ab17 renaming h325 → _p2mH325
open _root_.P2M7374ab17 renaming h326 → _p2mH326
open _root_.P2M7374ab17 renaming h324 → _p2mH324
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
theorem _root_.P2M7374ab17.h276 (security : ℕ) (profile : Palette security → ℝ) (output : Palette security) :
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
open _root_.P2M7374ab17 renaming h276 → _p2mH276
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h275 (security : ℕ) (output : Palette security) :
    1 / (8 * (Parameters.base security : ℝ) * Parameters.modulus security) ≤
      activation security * (primaryLaw security).weight output := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have hp : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
    simpa only [primaryLaw] using primaryProfile_atom_lower security output
  calc
    _ = (1 / (4 * (Parameters.base security : ℝ))) * (1 / (2 * (Parameters.modulus security : ℝ))) := by ring
    _ ≤ _ := mul_le_mul (FirstResponse.activation_lower_simple security) hp (by positivity) (activation_pos security).le
open _root_.P2M7374ab17 renaming h275 → _p2mH275
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h278 (security bits : ℕ) (output : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits) :
    1 / (32 * (Parameters.base security : ℝ) * Parameters.modulus security) ≤
      (LocalPairProgram.activationApprox security bits : ℝ) * (primary security bits output.val : ℝ) := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have ha := _p2mH164 security bits hfirst
  have hp := RationalProposalProgram.primary_lower security bits output
  calc
    _ = (1 / (8 * (Parameters.base security : ℝ))) * (1 / (4 * (Parameters.modulus security : ℝ))) := by ring
    _ ≤ _ := mul_le_mul ha hp (by positivity) (LocalPairProgram.activationApprox_bounds security bits).1
open _root_.P2M7374ab17 renaming h278 → _p2mH278
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h281 (security bits : ℕ) (output : Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(LocalPairProgram.activationApprox security bits : ℝ) * (primary security bits output.val : ℝ) -
      activation security * (primaryLaw security).weight output| ≤
      (1 / 2 + 64 * (Parameters.base security : ℝ) * Parameters.dimension security) * (1 / (2 : ℝ)^bits) := by
  have hp : |(primary security bits output.val : ℝ) - (primaryLaw security).weight output| ≤
      (64 * (Parameters.base security : ℝ) * Parameters.dimension security) * (1 / (2 : ℝ)^bits) := by
    simpa only [primaryLaw] using _p2mH318 security bits output hprecision hbudget
  have ha := _p2mH75 security bits
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
open _root_.P2M7374ab17 renaming h281 → _p2mH281
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h274 (security : ℕ) (profile : Palette security → ℝ) (bound : ℝ) (hb : 0 ≤ bound)
    (hprofile : ∀ color, |profile color| ≤ bound) (output : Palette security) :
    |actual security profile output| ≤ RationalTensorInverseProgram.actualBound security * bound := by
  have hq := FirstResponse.modulus_pos security
  have hbase := FirstResponse.base_pos security
  have hden := _p2mH275 security output
  have hpos : 0 < activation security * (primaryLaw security).weight output :=
    mul_pos (activation_pos security) (primaryReference_positive security output)
  rw [_p2mH276, abs_div, abs_of_pos hpos]
  calc
    _ ≤ (RationalDensityInverseProgram.inverseBound security * bound) /
      (activation security * (primaryLaw security).weight output) :=
      div_le_div_of_nonneg_right
        (_p2mH165 security profile bound hb hprofile output) hpos.le
    _ ≤ (RationalDensityInverseProgram.inverseBound security * bound) /
      (1 / (8 * (Parameters.base security : ℝ) * Parameters.modulus security)) :=
      div_le_div_of_nonneg_left (by unfold RationalDensityInverseProgram.inverseBound; positivity) (by positivity) hden
    _ = _ := by unfold RationalTensorInverseProgram.actualBound; ring_nf; simp only [inv_inv]
open _root_.P2M7374ab17 renaming h274 → _p2mH274
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h277 (security : ℕ) (first second : Palette security → ℝ)
    (error : ℝ) (he : 0 ≤ error) (hdiff : ∀ color, |first color - second color| ≤ error) (output : Palette security) :
    |actual security first output - actual security second output| ≤ RationalTensorInverseProgram.actualBound security * error := by
  have h := _p2mH274 security (first - second) error he hdiff output
  simpa only [map_sub, Pi.sub_apply] using h
open _root_.P2M7374ab17 renaming h277 → _p2mH277
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h283 (security : ℕ) (profile : Palette security → ℝ) (word : Fin 1 → Palette security) :
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
open _root_.P2M7374ab17 renaming h283 → _p2mH283
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h282 (security : ℕ) : 0 ≤ errorConstant security := by
  unfold errorConstant RationalDensityInverseProgram.inverseBound RationalFirstResponseProgram.inverseErrorConstant
  positivity
open _root_.P2M7374ab17 renaming h282 → _p2mH282
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h279 (security bits : ℕ) (profile : ℕ → ℚ) (bound : ℝ) (hb : 0 ≤ bound)
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
    apply le_trans _ (_p2mH275 security output)
    dsimp only [lower]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h := _p2mH167
    (RationalFirstResponseProgram.inverse security bits profile output.val : ℝ)
    ((FirstResponse.responseEquiv security).symm (fun color : Palette security => (profile color.val : ℝ)) output)
    ((LocalPairProgram.activationApprox security bits : ℝ) * (primary security bits output.val : ℝ))
    (activation security * (primaryLaw security).weight output) lower
    (RationalFirstResponseProgram.inverseErrorConstant security * bound * (1 / (2 : ℝ)^bits))
    ((1 / 2 + 64 * (Parameters.base security : ℝ) * Parameters.dimension security) * (1 / (2 : ℝ)^bits))
    (RationalDensityInverseProgram.inverseBound security * bound) (by dsimp only [lower]; positivity)
    (_p2mH278 security bits output hfirst) hprimary (by positivity) (by positivity)
    (by unfold RationalDensityInverseProgram.inverseBound; positivity)
    ((_p2mH233 security bits profile output bound hb hprofile hfirst).trans_eq (by ring))
    (_p2mH281 security bits output hprecision hbudget)
    (_p2mH165 security _ bound hb hprofile output)
  rw [current, Rat.cast_div, Rat.cast_mul, _p2mH276]
  apply h.trans_eq
  unfold errorConstant lower
  ring_nf
  simp only [inv_inv]
  ring
open _root_.P2M7374ab17 renaming h279 → _p2mH279
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h280 (security bits : ℕ) (computed : ℕ → ℚ) (profile : Palette security → ℝ)
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
    (add_le_add (_p2mH279 security bits computed bound hb hcomputed hfirst hprecision hbudget output)
      (_p2mH277 security _ profile profileError he hdiff output))
open _root_.P2M7374ab17 renaming h280 → _p2mH280
end
open _root_.P2M7374ab17 renaming h274 → _p2mH274
open _root_.P2M7374ab17 renaming h275 → _p2mH275
open _root_.P2M7374ab17 renaming h276 → _p2mH276
open _root_.P2M7374ab17 renaming h277 → _p2mH277
open _root_.P2M7374ab17 renaming h278 → _p2mH278
open _root_.P2M7374ab17 renaming h279 → _p2mH279
open _root_.P2M7374ab17 renaming h280 → _p2mH280
open _root_.P2M7374ab17 renaming h281 → _p2mH281
open _root_.P2M7374ab17 renaming h282 → _p2mH282
open _root_.P2M7374ab17 renaming h283 → _p2mH283
end CurrentAFT.RationalMassLiftProgram
open _root_.P2M7374ab17 renaming h274 → _p2mH274
open _root_.P2M7374ab17 renaming h275 → _p2mH275
open _root_.P2M7374ab17 renaming h276 → _p2mH276
open _root_.P2M7374ab17 renaming h277 → _p2mH277
open _root_.P2M7374ab17 renaming h278 → _p2mH278
open _root_.P2M7374ab17 renaming h279 → _p2mH279
open _root_.P2M7374ab17 renaming h280 → _p2mH280
open _root_.P2M7374ab17 renaming h281 → _p2mH281
open _root_.P2M7374ab17 renaming h282 → _p2mH282
open _root_.P2M7374ab17 renaming h283 → _p2mH283
end
open _root_.P2M7374ab17 renaming h279 → _p2mH279
open _root_.P2M7374ab17 renaming h274 → _p2mH274
open _root_.P2M7374ab17 renaming h281 → _p2mH281
open _root_.P2M7374ab17 renaming h278 → _p2mH278
open _root_.P2M7374ab17 renaming h283 → _p2mH283
open _root_.P2M7374ab17 renaming h277 → _p2mH277
open _root_.P2M7374ab17 renaming h275 → _p2mH275
open _root_.P2M7374ab17 renaming h282 → _p2mH282
open _root_.P2M7374ab17 renaming h280 → _p2mH280
open _root_.P2M7374ab17 renaming h276 → _p2mH276
section
namespace CurrentAFT.RationalBackgroundDensities
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls BackgroundCertificates BackgroundTranslations
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw centerLaw
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h108 (security : ℕ) (output : FirstHistogram.Palette security) :
    RationalMassLiftProgram.actual security (FringeCertificate.bodyDeviation security) output =
      FringeCertificate.primaryCertificateDensity security output := by
  rw [_p2mH276]
  unfold FringeCertificate.primaryCertificateDensity FringeCertificate.primaryCertificateProfile
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
open _root_.P2M7374ab17 renaming h108 → _p2mH108
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h110 (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    RationalMassLiftProgram.actual security (BackgroundTranslations.translationResidual security shift) output =
      BackgroundTranslations.residualCertificateDensity security shift output := by
  rw [_p2mH276]
  unfold BackgroundTranslations.residualCertificateDensity BackgroundTranslations.residualCertificateProfile
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
open _root_.P2M7374ab17 renaming h110 → _p2mH110
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h105 (security bits : ℕ) (output : FirstHistogram.Palette security) :
    |(RationalBackgroundProfiles.bodyDeviation security bits output.val:ℝ)| ≤ 2 := by
  have hn := (RationalProposalProgram.approximateBodyLaw security bits false).nonneg output
  have hu := (RationalProposalProgram.approximateBodyLaw security bits false).atom_le_one output
  have hq : (1:ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.pos
  have hi : 0 ≤ (Parameters.modulus security:ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hi' : (Parameters.modulus security:ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hq
  simp only [RationalBackgroundProfiles.bodyDeviation, RationalBackgroundProfiles.colors, Rat.cast_sub, one_div,
    Rat.cast_inv, Rat.cast_natCast, PublicParameterProgram.modulus_value, RationalProposalProgram.body_cast]
  rw [abs_le]
  constructor <;> linarith
open _root_.P2M7374ab17 renaming h105 → _p2mH105
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h111 (security bits : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    |(RationalBackgroundProfiles.residual security bits shift output.val:ℝ)| ≤ 2 := by
  have hu (color : FirstHistogram.Palette security) : |BackgroundTranslations.unsafePart security shift color| ≤ 1 := by
    rw [abs_of_nonneg (BackgroundTranslations.unsafePart_nonneg security shift color)]
    exact (BackgroundTranslations.unsafePart_le_shifted security shift color).trans ((shiftedSafeLaw security shift).atom_le_one color)
  have hc : |(RationalBackgroundProfiles.convolution security bits (RationalBackgroundProfiles.unsafeProfile security shift) output.val:ℝ)| ≤ 1 := by
    rw [_p2mH134]
    simp_rw [_p2mH146]
    exact _p2mH42 _ _ 1 (fun seed => hu _)
  have hm := BackgroundTranslations.unsafeMass_le_one security shift
  have hn := BackgroundTranslations.unsafeMass_nonneg security shift
  have hb := (RationalProposalProgram.approximateBodyLaw security bits false).atom_le_one output
  have hbn := (RationalProposalProgram.approximateBodyLaw security bits false).nonneg output
  simp only [RationalBackgroundProfiles.residual, Rat.cast_sub, Rat.cast_mul, _p2mH145,
    RationalProposalProgram.body_cast]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg hn, abs_of_nonneg hbn]
  exact (add_le_add hc (mul_le_mul hm hb hbn (by norm_num))).trans_eq (by norm_num)
open _root_.P2M7374ab17 renaming h111 → _p2mH111
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h109 (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(primary security bits output.val:ℝ)-FringeCertificate.primaryCertificateDensity security output| ≤
      primaryErrorConstant security*(1/(2:ℝ)^bits) := by
  rw [primary, ← _p2mH108]
  exact (_p2mH280 security bits (RationalBackgroundProfiles.bodyDeviation security bits)
    (FringeCertificate.bodyDeviation security) 2 (3/(2:ℝ)^bits) (by norm_num) (by positivity)
    (_p2mH105 security bits) (_p2mH133 security bits)
    hfirst hprecision hbudget output).trans_eq (by unfold primaryErrorConstant; ring)
open _root_.P2M7374ab17 renaming h109 → _p2mH109
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h112 (security bits : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(residual security bits shift output.val:ℝ)-BackgroundTranslations.residualCertificateDensity security shift output| ≤
      residualErrorConstant security*(1/(2:ℝ)^bits) := by
  rw [residual, ← _p2mH110]
  exact (_p2mH280 security bits (RationalBackgroundProfiles.residual security bits shift)
    (BackgroundTranslations.translationResidual security shift) 2 (6/(2:ℝ)^bits) (by norm_num) (by positivity)
    (_p2mH111 security bits shift) (_p2mH140 security bits shift)
    hfirst hprecision hbudget output).trans_eq (by unfold residualErrorConstant; ring)
open _root_.P2M7374ab17 renaming h112 → _p2mH112
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h113 (security bits : ℕ) (numerator : ℕ → ℚ) (profile : FirstHistogram.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hnum : ∀ color, (numerator color.val:ℝ) = profile color)
    (hbound : ∀ color, |profile color| ≤ bound) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(numerator output.val.val/RationalProposalProgram.center security bits output.val.val:ℚ)-
      profile output.val/(centerLaw security).weight output.val| ≤
      bound*bodyErrorConstant security*(1/(2:ℝ)^bits) := by
  let q : ℝ := Parameters.modulus security
  have hq : 0 < q := FirstResponse.modulus_pos security
  have ha := _p2mH310 security bits output
  have hb' : 1/(2*q) ≤ (centerLaw security).weight output.val := ActualControls.bodyReference_lower security output
  have hd : |(RationalProposalProgram.center security bits output.val.val:ℝ)-(centerLaw security).weight output.val| ≤
      centerErrorConstant security*(1/(2:ℝ)^bits) := by
    simpa only [centerLaw, centerErrorConstant] using _p2mH309 security bits output.val hprecision hbudget
  have hx := _p2mH167 (profile output.val) (profile output.val)
    (RationalProposalProgram.center security bits output.val.val:ℝ) ((centerLaw security).weight output.val)
    (1/(2*q)) 0 (centerErrorConstant security*(1/(2:ℝ)^bits)) bound (by positivity) ha hb'
    (by norm_num) (by unfold centerErrorConstant; positivity) hb (by simp) hd (hbound output.val)
  rw [Rat.cast_div, hnum]
  apply hx.trans_eq
  unfold bodyErrorConstant
  dsimp only [q]
  ring_nf
  simp only [inv_inv]
open _root_.P2M7374ab17 renaming h113 → _p2mH113
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h107 (security : ℕ) (output : SafePalette security) :
    BackgroundCertificates.bodyCertificateDensity security output.val =
      1-(safeLaw security).weight output.val/(centerLaw security).weight output.val := by
  have hb : (centerLaw security).weight output.val ≠ 0 := ne_of_gt (bodyReference_positive security output)
  unfold BackgroundCertificates.bodyCertificateDensity BackgroundCertificates.bodyCertificateProfile
  field_simp [hb]
open _root_.P2M7374ab17 renaming h107 → _p2mH107
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h106 (security bits : ℕ) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(body security bits output.val.val:ℝ)-BackgroundCertificates.bodyCertificateDensity security output.val| ≤
      bodyErrorConstant security*(1/(2:ℝ)^bits) := by
  have hs (color : FirstHistogram.Palette security) : |(safeLaw security).weight color| ≤ 1 := by
    rw [abs_of_nonneg ((safeLaw security).nonneg color)]
    exact (safeLaw security).atom_le_one color
  have hx := _p2mH113 security bits (RationalBackgroundProfiles.safe security) (safeLaw security).weight 1
    (by norm_num) (_p2mH141 security) hs output hprecision hbudget
  have he : (body security bits output.val.val:ℝ)-BackgroundCertificates.bodyCertificateDensity security output.val =
      -((RationalBackgroundProfiles.safe security output.val.val/RationalProposalProgram.center security bits output.val.val:ℚ)-
        (safeLaw security).weight output.val/(centerLaw security).weight output.val) := by
    rw [body, Rat.cast_sub, Rat.cast_one, _p2mH107]
    ring
  rw [he, abs_neg]
  simpa only [one_mul] using hx
open _root_.P2M7374ab17 renaming h106 → _p2mH106
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h114 (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    |BackgroundTranslations.safeSeedProfile security shift output| ≤ 2 := by
  let projectedLaw : FiniteDist (FirstHistogram.Palette security) :=
    { weight := BackgroundTranslations.projectedShiftProfile security shift
      nonneg := BackgroundTranslations.projectedShiftProfile_nonneg security shift
      sum_one := BackgroundTranslations.projectedShiftProfile_mass security shift }
  have hp0 := projectedLaw.nonneg output
  have hp1 := projectedLaw.atom_le_one output
  have hs0 := (safeLaw security).nonneg output
  have hs1 := (safeLaw security).atom_le_one output
  unfold BackgroundTranslations.safeSeedProfile
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg hp0, abs_of_nonneg hs0]
  exact (add_le_add hp1 hs1).trans_eq (by norm_num)
open _root_.P2M7374ab17 renaming h114 → _p2mH114
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h115 (security bits : ℕ) (shift : ℤ) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(seed security bits shift output.val.val:ℝ)-BackgroundTranslations.safeSeedDensity security shift output.val| ≤
      2*bodyErrorConstant security*(1/(2:ℝ)^bits) := by
  exact _p2mH113 security bits (RationalBackgroundProfiles.seedProfile security shift)
    (BackgroundTranslations.safeSeedProfile security shift) 2 (by norm_num)
    (_p2mH143 security shift) (_p2mH114 security shift) output hprecision hbudget
open _root_.P2M7374ab17 renaming h115 → _p2mH115
end
open _root_.P2M7374ab17 renaming h105 → _p2mH105
open _root_.P2M7374ab17 renaming h106 → _p2mH106
open _root_.P2M7374ab17 renaming h107 → _p2mH107
open _root_.P2M7374ab17 renaming h108 → _p2mH108
open _root_.P2M7374ab17 renaming h109 → _p2mH109
open _root_.P2M7374ab17 renaming h110 → _p2mH110
open _root_.P2M7374ab17 renaming h111 → _p2mH111
open _root_.P2M7374ab17 renaming h112 → _p2mH112
open _root_.P2M7374ab17 renaming h113 → _p2mH113
open _root_.P2M7374ab17 renaming h114 → _p2mH114
open _root_.P2M7374ab17 renaming h115 → _p2mH115
end CurrentAFT.RationalBackgroundDensities
open _root_.P2M7374ab17 renaming h105 → _p2mH105
open _root_.P2M7374ab17 renaming h106 → _p2mH106
open _root_.P2M7374ab17 renaming h107 → _p2mH107
open _root_.P2M7374ab17 renaming h108 → _p2mH108
open _root_.P2M7374ab17 renaming h109 → _p2mH109
open _root_.P2M7374ab17 renaming h110 → _p2mH110
open _root_.P2M7374ab17 renaming h111 → _p2mH111
open _root_.P2M7374ab17 renaming h112 → _p2mH112
open _root_.P2M7374ab17 renaming h113 → _p2mH113
open _root_.P2M7374ab17 renaming h114 → _p2mH114
open _root_.P2M7374ab17 renaming h115 → _p2mH115
end
open _root_.P2M7374ab17 renaming h107 → _p2mH107
open _root_.P2M7374ab17 renaming h114 → _p2mH114
open _root_.P2M7374ab17 renaming h111 → _p2mH111
open _root_.P2M7374ab17 renaming h105 → _p2mH105
open _root_.P2M7374ab17 renaming h112 → _p2mH112
open _root_.P2M7374ab17 renaming h108 → _p2mH108
open _root_.P2M7374ab17 renaming h106 → _p2mH106
open _root_.P2M7374ab17 renaming h115 → _p2mH115
open _root_.P2M7374ab17 renaming h110 → _p2mH110
open _root_.P2M7374ab17 renaming h109 → _p2mH109
open _root_.P2M7374ab17 renaming h113 → _p2mH113
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
private theorem _root_.P2M7374ab17.h332 (order : ℕ) (horder : 1 ≤ order) (arity : TruncatedArity order) :
    arity = primaryArity order horder ↔ arity.val.1.val = 1 ∧ arity.val.2.val = 0 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · intro h
    apply Subtype.ext
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
open _root_.P2M7374ab17 renaming h332 → _p2mH332
set_option maxRecDepth 8192
private theorem _root_.P2M7374ab17.h331 (order : ℕ) (horder : 1 ≤ order) (arity : TruncatedArity order) :
    arity = bodyArity order horder ↔ arity.val.1.val = 0 ∧ arity.val.2.val = 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · intro h
    apply Subtype.ext
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
open _root_.P2M7374ab17 renaming h331 → _p2mH331
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h152 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
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
    · have hfirst := mt (_p2mH332 order horder arity).mpr hp
      have hsecond := mt (_p2mH331 order horder arity).mpr hb
      simp only [firstTable, dif_neg hfirst, dif_neg hsecond, Pi.add_apply, primaryFamily, bodyFamily,
        Pi.single_eq_of_ne hp, Pi.single_eq_of_ne hb, Submodule.coe_zero, Pi.zero_apply, add_zero]
open _root_.P2M7374ab17 renaming h152 → _p2mH152
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h154 {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order)
    (first second : Primary → ℝ)
    (hf : ∑ color, primary.weight color*first color=0) (hs : ∑ color, primary.weight color*second color=0)
    (ht : ∑ color, primary.weight color*(first color+second color)=0) :
    primaryFamily primary body order horder (fun color => first color+second color) ht =
      primaryFamily primary body order horder first hf+primaryFamily primary body order horder second hs := by
  unfold primaryFamily
  rw [← Pi.single_add]
  congr 1
open _root_.P2M7374ab17 renaming h154 → _p2mH154
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h153 {Primary Body : Type*} (order : ℕ) (firstQ secondQ : ℕ → ℚ)
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
open _root_.P2M7374ab17 renaming h153 → _p2mH153
end
open _root_.P2M7374ab17 renaming h152 → _p2mH152
open _root_.P2M7374ab17 renaming h153 → _p2mH153
open _root_.P2M7374ab17 renaming h154 → _p2mH154
open _root_.P2M7374ab17 renaming h331 → _p2mH331
open _root_.P2M7374ab17 renaming h332 → _p2mH332
end CurrentAFT.RationalBackgroundTable
open _root_.P2M7374ab17 renaming h152 → _p2mH152
open _root_.P2M7374ab17 renaming h153 → _p2mH153
open _root_.P2M7374ab17 renaming h154 → _p2mH154
open _root_.P2M7374ab17 renaming h331 → _p2mH331
open _root_.P2M7374ab17 renaming h332 → _p2mH332
end
open _root_.P2M7374ab17 renaming h152 → _p2mH152
open _root_.P2M7374ab17 renaming h153 → _p2mH153
open _root_.P2M7374ab17 renaming h154 → _p2mH154
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
theorem _root_.P2M7374ab17.h148 (security order : ℕ) (horder : 1 ≤ order) :
    firstTable order (FringeCertificate.primaryCertificateDensity security)
      (fun color : SafePalette security => BackgroundCertificates.bodyCertificateDensity security color.val) =
      fun arity => (BackgroundFamilies.freeCertificate security order horder arity).val := by
  exact _p2mH152 (ProposalPrimary.primaryLaw security) (bodyReference security) order horder
    _ _ (FringeCertificate.primaryCertificateDensity_centered security)
    (BackgroundFamilies.safe_centered security _ (BackgroundCertificates.bodyCertificateDensity_centered security))
open _root_.P2M7374ab17 renaming h148 → _p2mH148
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h150 (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    firstTable order (fun color => FringeCertificate.primaryCertificateDensity security color+
      BackgroundTranslations.residualCertificateDensity security shift color)
      (fun color : SafePalette security => BackgroundTranslations.safeSeedDensity security shift color.val) =
      fun arity => (BackgroundFamilies.translationCertificate security order horder shift arity).val := by
  have hcenter : ∑ color, (ProposalPrimary.primaryLaw security).weight color*
      (FringeCertificate.primaryCertificateDensity security color+BackgroundTranslations.residualCertificateDensity security shift color)=0 := by
    simp only [mul_add, Finset.sum_add_distrib, FringeCertificate.primaryCertificateDensity_centered,
      BackgroundTranslations.residualCertificateDensity_centered, add_zero]
  rw [_p2mH152 (ProposalPrimary.primaryLaw security) (bodyReference security) order horder _ _ hcenter
    (BackgroundFamilies.safe_centered security _ (BackgroundTranslations.safeSeedDensity_centered security shift))]
  rw [_p2mH154 _ _ _ _ _ _ (FringeCertificate.primaryCertificateDensity_centered security)
    (BackgroundTranslations.residualCertificateDensity_centered security shift) hcenter]
  rfl
open _root_.P2M7374ab17 renaming h150 → _p2mH150
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h147 (security : ℕ) : 0 ≤ primaryErrorConstant security ∧
    0 ≤ residualErrorConstant security ∧ 0 ≤ bodyErrorConstant security := by
  simp only [primaryErrorConstant, residualErrorConstant, bodyErrorConstant, centerErrorConstant,
    RationalMassLiftProgram.errorConstant, RationalTensorInverseProgram.actualBound,
    RationalDensityInverseProgram.inverseBound, RationalFirstResponseProgram.inverseErrorConstant]
  exact ⟨by positivity, by positivity, by positivity⟩
open _root_.P2M7374ab17 renaming h147 → _p2mH147
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h149 (security bits order : ℕ) (horder : 1 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(free security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (BackgroundFamilies.freeCertificate security order horder arity).val colors centers| ≤
      freeErrorConstant security*(1/(2:ℝ)^bits) := by
  rcases _p2mH147 security with ⟨hprimaryNonneg, hresidualNonneg, hbodyNonneg⟩
  have hx := _p2mH153 order (RationalBackgroundDensities.primary security bits) (RationalBackgroundDensities.body security bits)
    (FringeCertificate.primaryCertificateDensity security)
    (fun color : SafePalette security => BackgroundCertificates.bodyCertificateDensity security color.val)
    Fin.val (fun color => color.val.val) (primaryErrorConstant security*(1/(2:ℝ)^bits)) (bodyErrorConstant security*(1/(2:ℝ)^bits))
    (by positivity) (by positivity)
    (fun color => _p2mH109 security bits color hfirst hprecision hbudget)
    (fun color => _p2mH106 security bits color hprecision hbudget) arity colors centers
  rw [_p2mH148 security order horder] at hx
  exact hx.trans_eq (by unfold freeErrorConstant; ring)
open _root_.P2M7374ab17 renaming h149 → _p2mH149
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h151 (security bits order : ℕ) (horder : 1 ≤ order) (shift : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(translation security bits order shift arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (BackgroundFamilies.translationCertificate security order horder shift arity).val colors centers| ≤
      translationErrorConstant security*(1/(2:ℝ)^bits) := by
  rcases _p2mH147 security with ⟨hprimaryNonneg, hresidualNonneg, hbodyNonneg⟩
  have hp (color : FirstHistogram.Palette security) :
      |((RationalBackgroundDensities.primary security bits color.val+RationalBackgroundDensities.residual security bits shift color.val:ℚ):ℝ)-
        (FringeCertificate.primaryCertificateDensity security color+BackgroundTranslations.residualCertificateDensity security shift color)| ≤
      (primaryErrorConstant security+residualErrorConstant security)*(1/(2:ℝ)^bits) := by
    rw [Rat.cast_add]
    have he : (RationalBackgroundDensities.primary security bits color.val:ℝ)+(RationalBackgroundDensities.residual security bits shift color.val:ℝ)-
        (FringeCertificate.primaryCertificateDensity security color+BackgroundTranslations.residualCertificateDensity security shift color) =
        ((RationalBackgroundDensities.primary security bits color.val:ℝ)-FringeCertificate.primaryCertificateDensity security color)+
        ((RationalBackgroundDensities.residual security bits shift color.val:ℝ)-BackgroundTranslations.residualCertificateDensity security shift color) := by ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add
      (_p2mH109 security bits color hfirst hprecision hbudget)
      (_p2mH112 security bits shift color hfirst hprecision hbudget)).trans_eq (by ring))
  have hx := _p2mH153 order
    (fun color => RationalBackgroundDensities.primary security bits color+RationalBackgroundDensities.residual security bits shift color)
    (RationalBackgroundDensities.seed security bits shift)
    (fun color => FringeCertificate.primaryCertificateDensity security color+BackgroundTranslations.residualCertificateDensity security shift color)
    (fun color : SafePalette security => BackgroundTranslations.safeSeedDensity security shift color.val)
    Fin.val (fun color => color.val.val)
    ((primaryErrorConstant security+residualErrorConstant security)*(1/(2:ℝ)^bits)) (2*bodyErrorConstant security*(1/(2:ℝ)^bits))
    (by positivity) (by positivity) hp
    (fun color => _p2mH115 security bits shift color hprecision hbudget) arity colors centers
  rw [_p2mH150 security order horder shift] at hx
  exact hx.trans_eq (by unfold translationErrorConstant; ring)
open _root_.P2M7374ab17 renaming h151 → _p2mH151
end
open _root_.P2M7374ab17 renaming h147 → _p2mH147
open _root_.P2M7374ab17 renaming h148 → _p2mH148
open _root_.P2M7374ab17 renaming h149 → _p2mH149
open _root_.P2M7374ab17 renaming h150 → _p2mH150
open _root_.P2M7374ab17 renaming h151 → _p2mH151
end CurrentAFT.RationalBackgroundProgram
open _root_.P2M7374ab17 renaming h147 → _p2mH147
open _root_.P2M7374ab17 renaming h148 → _p2mH148
open _root_.P2M7374ab17 renaming h149 → _p2mH149
open _root_.P2M7374ab17 renaming h150 → _p2mH150
open _root_.P2M7374ab17 renaming h151 → _p2mH151
end
open _root_.P2M7374ab17 renaming h150 → _p2mH150
open _root_.P2M7374ab17 renaming h149 → _p2mH149
open _root_.P2M7374ab17 renaming h151 → _p2mH151
open _root_.P2M7374ab17 renaming h147 → _p2mH147
open _root_.P2M7374ab17 renaming h148 → _p2mH148
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
theorem _root_.P2M7374ab17.h123 (security bits order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → ℕ) (centers : Fin arity.val.2.val → ℕ) :
    meanTranslation security bits order arity colors centers =
      ∑ scalar : Window (cutoff security),
        RationalProposalProgram.gaussianWeight security (cutoff security) bits scalar *
          RationalBackgroundProgram.translation security bits order scalar.val arity colors centers := by
  unfold meanTranslation
  exact (FiniteConvolutionProgram.windowIndexEquiv (cutoff security)).sum_comp
    (fun scalar : Window (cutoff security) =>
      RationalProposalProgram.gaussianWeight security (cutoff security) bits scalar *
        RationalBackgroundProgram.translation security bits order scalar.val arity colors centers)
open _root_.P2M7374ab17 renaming h123 → _p2mH123
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h116 (security : ℕ) : cutoff security = Parameters.sourceCutoff security-1 := by
  simp only [cutoff, Parameters.sourceCutoff, Parameters.base]
open _root_.P2M7374ab17 renaming h116 → _p2mH116
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h125 (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(translationCertificate security order horder shift arity).val colors centers| ≤ translationBound security order := by
  have hb : (1:ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by decide : 1≤2)
  have hn : LocalRaisingBounds.coefficientNorm security order (translationCertificate security order horder shift) ≤ 56 := by
    apply (translationCertificate_norm_decay security order horder shift).trans
    exact div_le_self (by norm_num) (one_le_pow₀ hb)
  exact (_p2mH35 security order (translationCertificate security order horder shift) arity colors centers).trans
    ((mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (by unfold translationBound; ring))
open _root_.P2M7374ab17 renaming h125 → _p2mH125
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h122 (security bits order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → FirstHistogram.Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    (meanTranslation security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ) =
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security-1) bits).expectation
        (fun scalar => (RationalBackgroundProgram.translation security bits order scalar.val arity
          (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)) := by
  rw [_p2mH123, Rat.cast_sum, _p2mH116]
  simp only [Rat.cast_mul, RationalProposalProgram.gaussianWeight_eq, FiniteDist.expectation, windowApproxLaw]
open _root_.P2M7374ab17 renaming h122 → _p2mH122
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h121 (security order : ℕ) (horder : 1 ≤ order) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → FirstHistogram.Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    (scalarLaw security).expectation (fun scalar => (translationCertificate security order horder scalar.val arity).val colors centers) =
      (BackgroundLinear.meanTranslation security order horder arity).val colors centers := by
  simp only [BackgroundLinear.meanTranslation, FiniteDist.expectation, Finset.sum_apply, Submodule.coe_sum, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul]
open _root_.P2M7374ab17 renaming h121 → _p2mH121
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h124 (security bits order : ℕ) (horder : 1 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(meanTranslation security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (BackgroundLinear.meanTranslation security order horder arity).val colors centers| ≤ meanErrorConstant security order*(1/(2:ℝ)^bits) := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security-1) bits
  let computed := fun scalar : MarkedPairSeed.Scalar security =>
    (RationalBackgroundProgram.translation security bits order scalar.val arity
      (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)
  let ideal := fun scalar : MarkedPairSeed.Scalar security => (translationCertificate security order horder scalar.val arity).val colors centers
  have hl1 := _p2mH16 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security-1) bits (_p2mH327 security) (_p2mH328 security).symm
  have hpoint := _p2mH42 approximate (computed-ideal)
    (RationalBackgroundProgram.translationErrorConstant security*(1/(2:ℝ)^bits))
    (fun scalar => _p2mH151 security bits order horder scalar.val hfirst hprecision hbudget arity colors centers)
  change |approximate.expectation (fun scalar => computed scalar-ideal scalar)| ≤ _ at hpoint
  rw [FiniteDist.expectation_sub] at hpoint
  have hsource := (_p2mH47 approximate (scalarLaw security) ideal
    (translationBound security order) (fun scalar => _p2mH125 security order horder scalar.val arity colors centers)).trans
    (mul_le_mul_of_nonneg_left hl1 (by unfold translationBound; positivity))
  rw [_p2mH122, ← _p2mH121 security order horder]
  exact (abs_sub_le _ (approximate.expectation ideal) _).trans ((add_le_add hpoint hsource).trans_eq (by unfold meanErrorConstant; ring))
open _root_.P2M7374ab17 renaming h124 → _p2mH124
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h117 (security : ℕ) : (freeMass security:ℝ) = ProposalPrimary.freeMass security := by
  simp only [freeMass, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_add, Rat.cast_ofNat, PublicParameterProgram.modulus_value,
    ProposalPrimary.freeMass, Parameters.bodySize_eq, Parameters.legCount_eq, Parameters.base, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
open _root_.P2M7374ab17 renaming h117 → _p2mH117
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h118 (security bits order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    (legLinear security bits order arity (fun index => (colors index).val)
      (fun index => (centers index).val.val):ℝ) =
      -(ProposalPrimary.freeMass security *
        (RationalBackgroundProgram.free security bits order arity (fun index => (colors index).val)
          (fun index => (centers index).val.val):ℝ) +
        (Parameters.modulus security:ℝ) *
        (meanTranslation security bits order arity (fun index => (colors index).val)
          (fun index => (centers index).val.val):ℝ)) / Parameters.legCount security := by
  simp only [legLinear, Rat.cast_div, Rat.cast_neg, Rat.cast_add, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat, _p2mH117,
    PublicParameterProgram.modulus_value, Parameters.legCount_eq, Parameters.base,
    Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
open _root_.P2M7374ab17 renaming h118 → _p2mH118
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h119 (security order : ℕ) (horder : 1 ≤ order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    -(ProposalPrimary.freeMass security * (freeCertificate security order horder arity).val colors centers +
      (Parameters.modulus security:ℝ) * (BackgroundLinear.meanTranslation security order horder arity).val colors centers) /
        Parameters.legCount security =
      (BackgroundLinear.legLinearCertificate security order horder arity).val colors centers := by
  simp only [BackgroundLinear.legLinearCertificate, Pi.add_apply, Pi.smul_apply,
    Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
  ring
open _root_.P2M7374ab17 renaming h119 → _p2mH119
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h120 (security bits order : ℕ) (horder : 1 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(legLinear security bits order arity (fun index => (colors index).val)
        (fun index => (centers index).val.val):ℝ) -
      (BackgroundLinear.legLinearCertificate security order horder arity).val colors centers| ≤
        linearErrorConstant security order * (1/(2:ℝ)^bits) := by
  have hf := _p2mH149 security bits order horder hfirst hprecision hbudget arity colors centers
  have hm := _p2mH124 security bits order horder hfirst hprecision hbudget arity colors centers
  have hfree := ProposalPrimary.freeMass_nonneg security
  have hq := (FirstResponse.modulus_pos security).le
  have hlegs := BackgroundLinear.legCount_pos security
  rw [_p2mH118, ← _p2mH119 security order horder arity colors centers]
  rw [show -(ProposalPrimary.freeMass security *
      (RationalBackgroundProgram.free security bits order arity (fun index => (colors index).val)
        (fun index => (centers index).val.val):ℝ) + (Parameters.modulus security:ℝ) *
      (meanTranslation security bits order arity (fun index => (colors index).val)
        (fun index => (centers index).val.val):ℝ)) / Parameters.legCount security -
      -(ProposalPrimary.freeMass security * (freeCertificate security order horder arity).val colors centers +
        (Parameters.modulus security:ℝ) * (BackgroundLinear.meanTranslation security order horder arity).val colors centers) /
        Parameters.legCount security =
      -(ProposalPrimary.freeMass security *
        ((RationalBackgroundProgram.free security bits order arity (fun index => (colors index).val)
          (fun index => (centers index).val.val):ℝ) - (freeCertificate security order horder arity).val colors centers) +
        (Parameters.modulus security:ℝ) *
        ((meanTranslation security bits order arity (fun index => (colors index).val)
          (fun index => (centers index).val.val):ℝ) -
          (BackgroundLinear.meanTranslation security order horder arity).val colors centers)) /
          Parameters.legCount security by ring]
  rw [abs_div, abs_neg, abs_of_pos hlegs]
  calc
    _ ≤ (ProposalPrimary.freeMass security * (RationalBackgroundProgram.freeErrorConstant security*(1/(2:ℝ)^bits)) +
        (Parameters.modulus security:ℝ) * (meanErrorConstant security order*(1/(2:ℝ)^bits))) /
          Parameters.legCount security := by
      apply div_le_div_of_nonneg_right _ hlegs.le
      exact (abs_add_le _ _).trans (by
        simpa only [abs_mul, abs_of_nonneg hfree, abs_of_nonneg hq] using
          add_le_add (mul_le_mul_of_nonneg_left hf hfree) (mul_le_mul_of_nonneg_left hm hq))
    _ = _ := by unfold linearErrorConstant; ring
open _root_.P2M7374ab17 renaming h120 → _p2mH120
end
open _root_.P2M7374ab17 renaming h116 → _p2mH116
open _root_.P2M7374ab17 renaming h117 → _p2mH117
open _root_.P2M7374ab17 renaming h118 → _p2mH118
open _root_.P2M7374ab17 renaming h119 → _p2mH119
open _root_.P2M7374ab17 renaming h120 → _p2mH120
open _root_.P2M7374ab17 renaming h121 → _p2mH121
open _root_.P2M7374ab17 renaming h122 → _p2mH122
open _root_.P2M7374ab17 renaming h123 → _p2mH123
open _root_.P2M7374ab17 renaming h124 → _p2mH124
open _root_.P2M7374ab17 renaming h125 → _p2mH125
end CurrentAFT.RationalBackgroundLinearProgram
open _root_.P2M7374ab17 renaming h116 → _p2mH116
open _root_.P2M7374ab17 renaming h117 → _p2mH117
open _root_.P2M7374ab17 renaming h118 → _p2mH118
open _root_.P2M7374ab17 renaming h119 → _p2mH119
open _root_.P2M7374ab17 renaming h120 → _p2mH120
open _root_.P2M7374ab17 renaming h121 → _p2mH121
open _root_.P2M7374ab17 renaming h122 → _p2mH122
open _root_.P2M7374ab17 renaming h123 → _p2mH123
open _root_.P2M7374ab17 renaming h124 → _p2mH124
open _root_.P2M7374ab17 renaming h125 → _p2mH125
end
open _root_.P2M7374ab17 renaming h119 → _p2mH119
open _root_.P2M7374ab17 renaming h124 → _p2mH124
open _root_.P2M7374ab17 renaming h120 → _p2mH120
open _root_.P2M7374ab17 renaming h118 → _p2mH118
open _root_.P2M7374ab17 renaming h121 → _p2mH121
open _root_.P2M7374ab17 renaming h123 → _p2mH123
open _root_.P2M7374ab17 renaming h125 → _p2mH125
open _root_.P2M7374ab17 renaming h117 → _p2mH117
open _root_.P2M7374ab17 renaming h122 → _p2mH122
open _root_.P2M7374ab17 renaming h116 → _p2mH116
section
namespace CurrentAFT.RationalMassCertificateTable
open AFT GradedControlAlgebra BackgroundFamilies PrimaryMassFamilies ActualControls
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalMassCertificateTable.massFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h273 (security order : ℕ) (horder : 1 ≤ order) (profile : FirstHistogram.Palette security → ℝ)
    (hcenter : PrimaryTensorInverse.MassCentered 1 (PrimaryMassFamilies.oneWordProfile profile))
    (hsymm : ∀ (permutation : Equiv.Perm (Fin 1)) word,
      PrimaryMassFamilies.oneWordProfile profile (word ∘ permutation) = PrimaryMassFamilies.oneWordProfile profile word) :
    RationalBackgroundTable.firstTable order (RationalMassLiftProgram.actual security profile) (fun _ : SafePalette security => (0:ℝ)) =
      fun arity => (PrimaryMassFamilies.massCertificateFamily security order 1 horder
        (PrimaryMassFamilies.oneWordProfile profile) hcenter hsymm arity).val := by
  funext arity colors centers
  by_cases hp : arity = BackgroundFamilies.primaryArity order horder
  · subst arity
    simp only [RationalBackgroundTable.firstTable, BackgroundFamilies.primaryArity, Fin.val_zero, and_self,
      PrimaryMassFamilies.massCertificateFamily, PrimaryMassFamilies.primaryArity, Pi.single_eq_same,
      PrimaryMassFamilies.massLiftKernel]
    exact (_p2mH283 security profile colors).symm
  · have hshape : ¬(arity.val.1.val=1 ∧ arity.val.2.val=0) := by
      intro hs
      apply hp
      apply Subtype.ext
      exact Prod.ext (Fin.ext hs.1) (Fin.ext hs.2)
    have hmass : arity ≠ PrimaryMassFamilies.primaryArity order 1 horder := hp
    simp only [RationalBackgroundTable.firstTable, dif_neg hshape, PrimaryMassFamilies.massCertificateFamily,
      Pi.single_eq_of_ne hmass, Submodule.coe_zero, Pi.zero_apply]
    split_ifs <;> rfl
open _root_.P2M7374ab17 renaming h273 → _p2mH273
end
open _root_.P2M7374ab17 renaming h273 → _p2mH273
end CurrentAFT.RationalMassCertificateTable
open _root_.P2M7374ab17 renaming h273 → _p2mH273
end
open _root_.P2M7374ab17 renaming h273 → _p2mH273
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
theorem _root_.P2M7374ab17.h304 (security bits : ℕ) (output : FirstHistogram.Palette security) :
    |(profile security bits output.val:ℝ)| ≤ 2 := by
  have hp0 := (RationalProposalProgram.approximatePrimaryLaw security bits).nonneg output
  have hp1 := (RationalProposalProgram.approximatePrimaryLaw security bits).atom_le_one output
  change 0 ≤ (RationalProposalProgram.primary security bits output.val:ℝ) at hp0
  change (RationalProposalProgram.primary security bits output.val:ℝ) ≤ 1 at hp1
  have hq : (1:ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast (Nat.succ_le_of_lt (Parameters.modulus_spec security).2.pos)
  have hu : 1/(Parameters.modulus security:ℝ) ≤ 1 := by
    exact (div_le_one (FirstResponse.modulus_pos security)).mpr hq
  simp only [profile, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    PublicParameterProgram.modulus_value]
  rw [abs_sub_le_iff]
  constructor <;> linarith [div_nonneg (show (0:ℝ)≤1 by norm_num) (FirstResponse.modulus_pos security).le]
open _root_.P2M7374ab17 renaming h304 → _p2mH304
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h305 (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(profile security bits output.val:ℝ)-PrimaryDeviationCertificate.deviation security output| ≤
      profileErrorConstant security*(1/(2:ℝ)^bits) := by
  simpa only [profile, Rat.cast_sub, Rat.cast_div, Rat.cast_inv, Rat.cast_one, Rat.cast_natCast,
    PublicParameterProgram.modulus_value, PrimaryDeviationCertificate.deviation, Pi.sub_apply,
    FringeCertificate.uniformProfile, one_div, sub_sub_sub_cancel_right, profileErrorConstant, primaryLaw] using
    _p2mH318 security bits output hprecision hbudget
open _root_.P2M7374ab17 renaming h305 → _p2mH305
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h302 (security order : ℕ) (horder : 1 ≤ order) :
    RationalBackgroundTable.firstTable order
      (RationalMassLiftProgram.actual security (PrimaryDeviationCertificate.deviation security))
      (fun _ : SafePalette security => (0:ℝ)) =
      fun arity => (PrimaryDeviationCertificate.certificate security order horder arity).val := by
  exact _p2mH273 security order horder (PrimaryDeviationCertificate.deviation security)
    (PrimaryMassFamilies.oneWordProfile_centered _ (PrimaryDeviationCertificate.deviation_mass security))
    (PrimaryMassFamilies.oneWordProfile_symmetric _)
open _root_.P2M7374ab17 renaming h302 → _p2mH302
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h303 (security : ℕ) : 0 ≤ errorConstant security := by
  simp only [errorConstant, profileErrorConstant, RationalMassLiftProgram.errorConstant,
    RationalTensorInverseProgram.actualBound, RationalDensityInverseProgram.inverseBound,
    RationalFirstResponseProgram.inverseErrorConstant]
  positivity
open _root_.P2M7374ab17 renaming h303 → _p2mH303
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h301 (security bits order : ℕ) (horder : 1 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (PrimaryDeviationCertificate.certificate security order horder arity).val colors centers| ≤
      errorConstant security*(1/(2:ℝ)^bits) := by
  have hl (primary : FirstHistogram.Palette security) :
      |(RationalMassLiftProgram.current security bits (profile security bits) primary.val:ℝ)-
        RationalMassLiftProgram.actual security (PrimaryDeviationCertificate.deviation security) primary| ≤
        errorConstant security*(1/(2:ℝ)^bits) := by
    exact (_p2mH280 security bits (profile security bits)
      (PrimaryDeviationCertificate.deviation security) 2 (profileErrorConstant security*(1/(2:ℝ)^bits))
      (by norm_num) (by unfold profileErrorConstant; positivity)
      (_p2mH304 security bits) (fun output => _p2mH305 security bits output hprecision hbudget)
      hfirst hprecision hbudget primary).trans_eq (by unfold errorConstant; ring)
  have hx := _p2mH153 order
    (RationalMassLiftProgram.current security bits (profile security bits)) (fun _ => 0)
    (RationalMassLiftProgram.actual security (PrimaryDeviationCertificate.deviation security)) (fun _ : SafePalette security => 0)
    Fin.val (fun color => color.val.val) (errorConstant security*(1/(2:ℝ)^bits)) 0
    (mul_nonneg (_p2mH303 security) (by positivity)) (by norm_num) hl (fun _ => by norm_num) arity colors centers
  rw [_p2mH302 security order horder] at hx
  simpa only [add_zero,current] using hx
open _root_.P2M7374ab17 renaming h301 → _p2mH301
end
open _root_.P2M7374ab17 renaming h301 → _p2mH301
open _root_.P2M7374ab17 renaming h302 → _p2mH302
open _root_.P2M7374ab17 renaming h303 → _p2mH303
open _root_.P2M7374ab17 renaming h304 → _p2mH304
open _root_.P2M7374ab17 renaming h305 → _p2mH305
end CurrentAFT.RationalPrimaryDeviationProgram
open _root_.P2M7374ab17 renaming h301 → _p2mH301
open _root_.P2M7374ab17 renaming h302 → _p2mH302
open _root_.P2M7374ab17 renaming h303 → _p2mH303
open _root_.P2M7374ab17 renaming h304 → _p2mH304
open _root_.P2M7374ab17 renaming h305 → _p2mH305
end
open _root_.P2M7374ab17 renaming h304 → _p2mH304
open _root_.P2M7374ab17 renaming h303 → _p2mH303
open _root_.P2M7374ab17 renaming h302 → _p2mH302
open _root_.P2M7374ab17 renaming h305 → _p2mH305
open _root_.P2M7374ab17 renaming h301 → _p2mH301
section
namespace CurrentAFT.RationalMarkedSeedProgram
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls MarkedPairSeed MarkedPairLeading
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw centerLaw
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h260 (security : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary output : FirstHistogram.Palette security) :
    (fixedAnchor security primary.val scalar.val output.val:ℝ) = (MarkedPairLeading.paletteAnchor security scalar primary).weight output := by
  unfold fixedAnchor
  rw [colors, PublicParameterProgram.modulus_value]
  have hA : (security+2)^48 = Parameters.anchorWidth security := by simp only [anchorWidth_eq, Parameters.base]
  rw [hA]
  exact RationalProposalProgram.anchorKernel_cast security primary output (-scalar.val)
    (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)
open _root_.P2M7374ab17 renaming h260 → _p2mH260
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h263 (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(rawDensity security bits primary.val scalar.val output.val.val:ℝ)-MarkedPairSeed.rawDensity security scalar primary output| ≤
      RationalBackgroundDensities.bodyErrorConstant security*(1/(2:ℝ)^bits) := by
  have hx := _p2mH113 security bits (fixedAnchor security primary.val scalar.val)
    (MarkedPairLeading.paletteAnchor security scalar primary).weight 1 (by norm_num)
    (_p2mH260 security scalar primary)
    (fun color => by
      rw [abs_of_nonneg ((MarkedPairLeading.paletteAnchor security scalar primary).nonneg color)]
      exact (MarkedPairLeading.paletteAnchor security scalar primary).atom_le_one color)
    output hprecision hbudget
  simpa only [rawDensity, MarkedPairSeed.rawDensity, MarkedPairSeed.fixedAnchor,
    ActualControls.bodyReference,ActualControls.supportedLaw,MarkedPairLeading.paletteAnchor,one_mul] using hx
open _root_.P2M7374ab17 renaming h263 → _p2mH263
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h262 (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security) :
    |(rawDensity security bits primary.val scalar.val output.val.val:ℝ)| ≤ 2*(Parameters.modulus security:ℝ) := by
  have hq := FirstResponse.modulus_pos security
  have hl := _p2mH310 security bits output
  have hp : 0 < (RationalProposalProgram.center security bits output.val.val:ℝ) := (by positivity : (0:ℝ)<1/(2*(Parameters.modulus security:ℝ))).trans_le hl
  rw [rawDensity, Rat.cast_div, _p2mH260, abs_div,
    abs_of_nonneg ((MarkedPairLeading.paletteAnchor security scalar primary).nonneg output.val), abs_of_pos hp]
  calc
    _ ≤ 1/(RationalProposalProgram.center security bits output.val.val:ℝ) :=
      div_le_div_of_nonneg_right ((MarkedPairLeading.paletteAnchor security scalar primary).atom_le_one output.val) hp.le
    _ ≤ 1/(1/(2*(Parameters.modulus security:ℝ))) := one_div_le_one_div_of_le (by positivity) hl
    _ = _ := by field_simp
open _root_.P2M7374ab17 renaming h262 → _p2mH262
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h264 (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security) :
    |(secondCentered security bits primary.val scalar.val output.val.val:ℝ)| ≤ 2*(Parameters.modulus security:ℝ)+1 := by
  rw [secondCentered, Rat.cast_sub, Rat.cast_one]
  exact (abs_sub _ _).trans (add_le_add (_p2mH262 security bits scalar primary output) (by norm_num))
open _root_.P2M7374ab17 renaming h264 → _p2mH264
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h265 (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(secondCentered security bits primary.val scalar.val output.val.val:ℝ)-MarkedPairSeed.secondCentered security scalar primary output| ≤
      RationalBackgroundDensities.bodyErrorConstant security*(1/(2:ℝ)^bits) := by
  simp only [secondCentered, Rat.cast_sub, Rat.cast_one, MarkedPairSeed.secondCentered]
  convert _p2mH263 security bits scalar primary output hprecision hbudget using 1
  congr 1
  ring
open _root_.P2M7374ab17 renaming h265 → _p2mH265
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h267 (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security) (output : SafePalette security) :
    (secondMean security bits scalar.val output.val.val:ℝ) =
      (RationalProposalProgram.approximatePrimaryLaw security bits).expectation
        (fun primary => (secondCentered security bits primary.val scalar.val output.val.val:ℝ)) := by
  unfold secondMean
  rw [Rat.cast_sum]
  have hq : colors security = Parameters.modulus security := PublicParameterProgram.modulus_value security
  rw [hq]
  simp only [FiniteDist.expectation, RationalProposalProgram.approximatePrimaryLaw, Rat.cast_mul]
open _root_.P2M7374ab17 renaming h267 → _p2mH267
end
open _root_.P2M7374ab17 renaming h260 → _p2mH260
open _root_.P2M7374ab17 renaming h262 → _p2mH262
open _root_.P2M7374ab17 renaming h263 → _p2mH263
open _root_.P2M7374ab17 renaming h264 → _p2mH264
open _root_.P2M7374ab17 renaming h265 → _p2mH265
open _root_.P2M7374ab17 renaming h267 → _p2mH267
end CurrentAFT.RationalMarkedSeedProgram
open _root_.P2M7374ab17 renaming h260 → _p2mH260
open _root_.P2M7374ab17 renaming h262 → _p2mH262
open _root_.P2M7374ab17 renaming h263 → _p2mH263
open _root_.P2M7374ab17 renaming h264 → _p2mH264
open _root_.P2M7374ab17 renaming h265 → _p2mH265
open _root_.P2M7374ab17 renaming h267 → _p2mH267
end
open _root_.P2M7374ab17 renaming h263 → _p2mH263
open _root_.P2M7374ab17 renaming h267 → _p2mH267
open _root_.P2M7374ab17 renaming h260 → _p2mH260
open _root_.P2M7374ab17 renaming h264 → _p2mH264
open _root_.P2M7374ab17 renaming h262 → _p2mH262
open _root_.P2M7374ab17 renaming h265 → _p2mH265
section
namespace CurrentAFT.RationalFiniteMean
open AFT
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h223 {State : Type*} [Fintype State]
    (reference approximate : FiniteDist State) (value computed : State → ℝ)
    (pointError atomError bound : ℝ) (_ha : 0 ≤ atomError) (hb : 0 ≤ bound)
    (hpoint : ∀ state, |computed state-value state| ≤ pointError)
    (hatom : ∀ state, |approximate.weight state-reference.weight state| ≤ atomError)
    (hbound : ∀ state, |value state| ≤ bound) :
    |approximate.expectation computed-reference.expectation value| ≤
      pointError+bound*((Fintype.card State:ℝ)*atomError) := by
  have hfirst := _p2mH42 approximate (fun state => computed state-value state) pointError hpoint
  rw [FiniteDist.expectation_sub] at hfirst
  have hl1 : (∑ state, |approximate.weight state-reference.weight state|) ≤ (Fintype.card State:ℝ)*atomError := by
    exact (Finset.sum_le_sum (s := Finset.univ) (fun state _ => hatom state)).trans_eq (by simp)
  have hsecond := (_p2mH47 approximate reference value bound hbound).trans
    (mul_le_mul_of_nonneg_left hl1 hb)
  exact (abs_sub_le _ (approximate.expectation value) _).trans (add_le_add hfirst hsecond)
open _root_.P2M7374ab17 renaming h223 → _p2mH223
end CurrentAFT.RationalFiniteMean
open _root_.P2M7374ab17 renaming h223 → _p2mH223
end
open _root_.P2M7374ab17 renaming h223 → _p2mH223
namespace CurrentAFT.RationalFiniteMean
end CurrentAFT.RationalFiniteMean
section
namespace CurrentAFT.RationalMarkedSeedProgram
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls MarkedPairSeed
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw centerLaw
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h258 (security : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security) :
    |MarkedPairSeed.secondCentered security scalar primary output| ≤ profileBound security := by
  have hq := FirstResponse.modulus_pos security
  have hl := ActualControls.bodyReference_lower security output
  have hp := ActualControls.bodyReference_positive security output
  have hraw : |MarkedPairSeed.rawDensity security scalar primary output| ≤ 2*(Parameters.modulus security:ℝ) := by
    rw [MarkedPairSeed.rawDensity, abs_div, abs_of_nonneg ((MarkedPairSeed.fixedAnchor security scalar primary).nonneg output), abs_of_pos hp]
    calc
      _ ≤ 1/(bodyReference security).weight output := div_le_div_of_nonneg_right ((MarkedPairSeed.fixedAnchor security scalar primary).atom_le_one output) hp.le
      _ ≤ 1/(1/(2*(Parameters.modulus security:ℝ))) := one_div_le_one_div_of_le (by positivity) hl
      _ = _ := by field_simp
  exact (abs_sub _ _).trans (add_le_add hraw (by norm_num))
open _root_.P2M7374ab17 renaming h258 → _p2mH258
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h266 (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security) (output : SafePalette security) :
    |(secondMean security bits scalar.val output.val.val:ℝ)| ≤ profileBound security := by
  rw [_p2mH267]
  exact _p2mH42 _ _ _ (fun color => _p2mH264 security bits scalar color output)
open _root_.P2M7374ab17 renaming h266 → _p2mH266
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h259 (security : ℕ) (scalar : MarkedPairSeed.Scalar security) (output : SafePalette security) :
    |MarkedPairSeed.secondMean security scalar output| ≤ profileBound security :=
  _p2mH42 _ _ _ (fun color => _p2mH258 security scalar color output)
open _root_.P2M7374ab17 renaming h259 → _p2mH259
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h268 (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(secondMean security bits scalar.val output.val.val:ℝ)-MarkedPairSeed.secondMean security scalar output| ≤
      meanErrorConstant security*(1/(2:ℝ)^bits) := by
  rw [_p2mH267]
  have hp (color : FirstHistogram.Palette security) :
      |(RationalProposalProgram.approximatePrimaryLaw security bits).weight color-(primaryLaw security).weight color| ≤
      primaryErrorConstant security*(1/(2:ℝ)^bits) := by
    simpa only [RationalProposalProgram.approximatePrimaryLaw, primaryLaw, primaryErrorConstant] using
      _p2mH318 security bits color hprecision hbudget
  have hx := _p2mH223 (primaryLaw security) (RationalProposalProgram.approximatePrimaryLaw security bits)
    (fun color => MarkedPairSeed.secondCentered security scalar color output)
    (fun color => (secondCentered security bits color.val scalar.val output.val.val:ℝ))
    (RationalBackgroundDensities.bodyErrorConstant security*(1/(2:ℝ)^bits))
    (primaryErrorConstant security*(1/(2:ℝ)^bits)) (profileBound security)
    (by unfold primaryErrorConstant; positivity) (by unfold profileBound; positivity)
    (fun color => _p2mH265 security bits scalar color output hprecision hbudget) hp
    (fun color => _p2mH258 security scalar color output)
  exact hx.trans_eq (by unfold meanErrorConstant; simp only [Fintype.card_fin]; ring)
open _root_.P2M7374ab17 renaming h268 → _p2mH268
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h271 (security bits : ℕ) (primary : FirstHistogram.Palette security) :
    |(uniformRelative security bits primary.val:ℝ)| ≤ 4 := by
  have hq := FirstResponse.modulus_pos security
  have hl := RationalProposalProgram.primary_lower security bits primary
  have hp : 0 < (RationalProposalProgram.primary security bits primary.val:ℝ) := (by positivity : (0:ℝ)<1/(4*(Parameters.modulus security:ℝ))).trans_le hl
  simp only [uniformRelative, colors, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, PublicParameterProgram.modulus_value]
  rw [abs_div, abs_of_pos (one_div_pos.mpr hq), abs_of_pos hp]
  calc
    _ ≤ (1/(Parameters.modulus security:ℝ))/(1/(4*(Parameters.modulus security:ℝ))) := div_le_div_of_nonneg_left (by positivity) (by positivity) hl
    _ = _ := by field_simp
open _root_.P2M7374ab17 renaming h271 → _p2mH271
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h272 (security bits : ℕ) (primary : FirstHistogram.Palette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(uniformRelative security bits primary.val:ℝ)-MarkedPairSeed.uniformRelative security primary| ≤
      uniformErrorConstant security*(1/(2:ℝ)^bits) := by
  let q : ℝ := Parameters.modulus security
  have hq : 0 < q := FirstResponse.modulus_pos security
  have hq1 : 1 ≤ q := by
    change (1:ℝ) ≤ (Parameters.modulus security:ℝ)
    exact_mod_cast (Nat.succ_le_of_lt (Parameters.modulus_spec security).2.pos)
  have hr : 1/(4*q) ≤ (primaryLaw security).weight primary := by
    apply le_trans _ (show 1/(2*q) ≤ (primaryLaw security).weight primary by simpa only [primaryLaw] using primaryProfile_atom_lower security primary)
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have ha := RationalProposalProgram.primary_lower security bits primary
  have hd : |(RationalProposalProgram.primary security bits primary.val:ℝ)-(primaryLaw security).weight primary| ≤ primaryErrorConstant security*(1/(2:ℝ)^bits) := by
    simpa only [primaryLaw, primaryErrorConstant] using _p2mH318 security bits primary hprecision hbudget
  have hv : |1/q| ≤ 1 := by rw [abs_of_pos (one_div_pos.mpr hq)]; simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hq1
  have hx := _p2mH167 (1/q) (1/q)
    (RationalProposalProgram.primary security bits primary.val:ℝ) ((primaryLaw security).weight primary)
    (1/(4*q)) 0 (primaryErrorConstant security*(1/(2:ℝ)^bits)) 1 (by positivity) ha hr
    (by norm_num) (by unfold primaryErrorConstant; positivity) (by norm_num) (by simp) hd hv
  simp only [uniformRelative, colors, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, PublicParameterProgram.modulus_value,
    MarkedPairSeed.uniformRelative, FringeCertificate.uniformProfile]
  have he : 0/(1/(4*q))+1*(primaryErrorConstant security*(1/(2:ℝ)^bits))/(1/(4*q))^2 =
      uniformErrorConstant security*(1/(2:ℝ)^bits) := by
    unfold uniformErrorConstant
    dsimp only [q]
    ring_nf
    simp only [inv_inv]
  simpa only [q, one_div] using hx.trans_eq he
open _root_.P2M7374ab17 renaming h272 → _p2mH272
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h269 (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security) :
    |(seedDensity security bits primary.val scalar.val output.val.val:ℝ)| ≤ 5*profileBound security := by
  rw [seedDensity, Rat.cast_sub, Rat.cast_mul]
  apply (abs_sub _ _).trans
  rw [abs_mul]
  exact (add_le_add (_p2mH264 security bits scalar primary output)
    (mul_le_mul (_p2mH271 security bits primary) (_p2mH266 security bits scalar output)
      (abs_nonneg _) (by norm_num))).trans_eq (by unfold profileBound; ring)
open _root_.P2M7374ab17 renaming h269 → _p2mH269
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h270 (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(seedDensity security bits primary.val scalar.val output.val.val:ℝ)-MarkedPairSeed.seedDensity security scalar primary output| ≤
      seedErrorConstant security*(1/(2:ℝ)^bits) := by
  let U : ℝ := uniformRelative security bits primary.val
  let V := MarkedPairSeed.uniformRelative security primary
  let M : ℝ := secondMean security bits scalar.val output.val.val
  let N := MarkedPairSeed.secondMean security scalar output
  have hu : |U| ≤ 4 := _p2mH271 security bits primary
  have hm : |N| ≤ profileBound security := _p2mH259 security scalar output
  have heU : |U-V| ≤ uniformErrorConstant security*(1/(2:ℝ)^bits) := _p2mH272 security bits primary hprecision hbudget
  have heM : |M-N| ≤ meanErrorConstant security*(1/(2:ℝ)^bits) := _p2mH268 security bits scalar output hprecision hbudget
  have hprod : |U*M-V*N| ≤ (4*meanErrorConstant security+profileBound security*uniformErrorConstant security)*(1/(2:ℝ)^bits) := by
    have hid : U*M-V*N = U*(M-N)+(U-V)*N := by ring
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact (add_le_add (mul_le_mul hu heM (abs_nonneg _) (by norm_num))
      (mul_le_mul heU hm (abs_nonneg _) (by unfold uniformErrorConstant primaryErrorConstant; positivity))).trans_eq (by ring)
  have heC := _p2mH265 security bits scalar primary output hprecision hbudget
  simp only [seedDensity, Rat.cast_sub, Rat.cast_mul, MarkedPairSeed.seedDensity]
  change |(secondCentered security bits primary.val scalar.val output.val.val:ℝ)-U*M-
    (MarkedPairSeed.secondCentered security scalar primary output-V*N)| ≤ _
  rw [show (secondCentered security bits primary.val scalar.val output.val.val:ℝ)-U*M-
      (MarkedPairSeed.secondCentered security scalar primary output-V*N) =
    ((secondCentered security bits primary.val scalar.val output.val.val:ℝ)-MarkedPairSeed.secondCentered security scalar primary output)-(U*M-V*N) by ring]
  exact (abs_sub _ _).trans ((add_le_add heC hprod).trans_eq (by unfold seedErrorConstant; ring))
open _root_.P2M7374ab17 renaming h270 → _p2mH270
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h261 (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(inverseDensity security bits scalar.val primary.val output.val.val:ℝ)-
      MarkedPairCertificates.inverseDensity security scalar primary output| ≤ inverseErrorConstant security*(1/(2:ℝ)^bits) := by
  let computed : FirstHistogram.Palette security → ℝ := fun color => seedDensity security bits color.val scalar.val output.val.val
  let ideal : FirstHistogram.Palette security → ℝ := fun color => MarkedPairSeed.seedDensity security scalar color output
  have hQ := _p2mH166 security bits
    (fun color => seedDensity security bits color scalar.val output.val.val) primary (5*profileBound security)
    (by unfold profileBound; positivity) (fun color => _p2mH269 security bits scalar color output) hfirst hprecision hbudget
  have hR := _p2mH325 security (computed-ideal)
    (seedErrorConstant security*(1/(2:ℝ)^bits))
    (by
      unfold seedErrorConstant meanErrorConstant profileBound uniformErrorConstant primaryErrorConstant
        RationalBackgroundDensities.bodyErrorConstant RationalBackgroundDensities.centerErrorConstant
      positivity)
    (fun color => _p2mH270 security bits scalar color output hprecision hbudget) primary
  have hdiff : |PrimaryTensorInverse.densityInverse security computed primary-PrimaryTensorInverse.densityInverse security ideal primary| ≤
      RationalTensorInverseProgram.actualBound security*(seedErrorConstant security*(1/(2:ℝ)^bits)) := by
    simpa only [map_sub, Pi.sub_apply] using hR
  exact (abs_sub_le _ (PrimaryTensorInverse.densityInverse security computed primary) _).trans
    ((add_le_add hQ hdiff).trans_eq (by unfold inverseErrorConstant; ring))
open _root_.P2M7374ab17 renaming h261 → _p2mH261
end
open _root_.P2M7374ab17 renaming h258 → _p2mH258
open _root_.P2M7374ab17 renaming h259 → _p2mH259
open _root_.P2M7374ab17 renaming h261 → _p2mH261
open _root_.P2M7374ab17 renaming h266 → _p2mH266
open _root_.P2M7374ab17 renaming h268 → _p2mH268
open _root_.P2M7374ab17 renaming h269 → _p2mH269
open _root_.P2M7374ab17 renaming h270 → _p2mH270
open _root_.P2M7374ab17 renaming h271 → _p2mH271
open _root_.P2M7374ab17 renaming h272 → _p2mH272
end CurrentAFT.RationalMarkedSeedProgram
open _root_.P2M7374ab17 renaming h258 → _p2mH258
open _root_.P2M7374ab17 renaming h259 → _p2mH259
open _root_.P2M7374ab17 renaming h261 → _p2mH261
open _root_.P2M7374ab17 renaming h266 → _p2mH266
open _root_.P2M7374ab17 renaming h268 → _p2mH268
open _root_.P2M7374ab17 renaming h269 → _p2mH269
open _root_.P2M7374ab17 renaming h270 → _p2mH270
open _root_.P2M7374ab17 renaming h271 → _p2mH271
open _root_.P2M7374ab17 renaming h272 → _p2mH272
end
open _root_.P2M7374ab17 renaming h266 → _p2mH266
open _root_.P2M7374ab17 renaming h258 → _p2mH258
open _root_.P2M7374ab17 renaming h259 → _p2mH259
open _root_.P2M7374ab17 renaming h271 → _p2mH271
open _root_.P2M7374ab17 renaming h272 → _p2mH272
open _root_.P2M7374ab17 renaming h268 → _p2mH268
open _root_.P2M7374ab17 renaming h270 → _p2mH270
open _root_.P2M7374ab17 renaming h269 → _p2mH269
open _root_.P2M7374ab17 renaming h261 → _p2mH261
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
theorem _root_.P2M7374ab17.h250 (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ideal security order scalar = fun arity => (markedMixedCertificate security order horder scalar arity).val := by
  funext arity colors centers
  by_cases h : arity = mixedArity order horder
  · subst arity
    simp [ideal, markedMixedCertificate, mixedArity, mixedKernel]
  · have hshape : ¬(arity.val.1.val=1 ∧ arity.val.2.val=1) := by
      intro hs
      apply h
      apply Subtype.ext
      exact Prod.ext (Fin.ext hs.1) (Fin.ext hs.2)
    simp only [ideal, dif_neg hshape, markedMixedCertificate, Pi.single_eq_of_ne h, Submodule.coe_zero, Pi.zero_apply]
open _root_.P2M7374ab17 renaming h250 → _p2mH250
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h251 (security : ℕ) : 0 ≤ RationalMarkedSeedProgram.inverseErrorConstant security := by
  simp only [RationalMarkedSeedProgram.inverseErrorConstant, RationalMarkedSeedProgram.seedErrorConstant, RationalMarkedSeedProgram.meanErrorConstant, RationalMarkedSeedProgram.profileBound, RationalMarkedSeedProgram.uniformErrorConstant, RationalMarkedSeedProgram.primaryErrorConstant, RationalBackgroundDensities.bodyErrorConstant, RationalBackgroundDensities.centerErrorConstant, RationalDensityInverseProgram.errorConstant, RationalDensityInverseProgram.inverseBound, RationalTensorInverseProgram.actualBound, RationalFirstResponseProgram.inverseErrorConstant]
  positivity
open _root_.P2M7374ab17 renaming h251 → _p2mH251
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h249 (security bits order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order scalar.val arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (markedMixedCertificate security order horder scalar arity).val colors centers| ≤
      RationalMarkedSeedProgram.inverseErrorConstant security*(1/(2:ℝ)^bits) := by
  have he := congrFun (congrFun (congrFun (_p2mH250 security order horder scalar) arity) colors) centers
  rw [← he]
  unfold current ideal
  split_ifs
  · exact _p2mH261 security bits scalar _ _ hfirst hprecision hbudget
  · simpa only [Rat.cast_zero, sub_self, abs_zero] using mul_nonneg (_p2mH251 security) (by positivity : (0:ℝ) ≤ 1/2^bits)
open _root_.P2M7374ab17 renaming h249 → _p2mH249
end
open _root_.P2M7374ab17 renaming h249 → _p2mH249
open _root_.P2M7374ab17 renaming h250 → _p2mH250
open _root_.P2M7374ab17 renaming h251 → _p2mH251
end CurrentAFT.RationalMarkedCertificateProgram
open _root_.P2M7374ab17 renaming h249 → _p2mH249
open _root_.P2M7374ab17 renaming h250 → _p2mH250
open _root_.P2M7374ab17 renaming h251 → _p2mH251
end
open _root_.P2M7374ab17 renaming h250 → _p2mH250
open _root_.P2M7374ab17 renaming h249 → _p2mH249
open _root_.P2M7374ab17 renaming h251 → _p2mH251
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
theorem _root_.P2M7374ab17.h257 (security order : ℕ) (horder : 1 ≤ order) :
    ∀ arity colors centers,
      |data security order (PrimaryDeviationCertificate.certificate security order horder) arity colors centers| ≤ primaryBound security order := by
  have hb : (1:ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  exact _p2mH102 security order _ 24 ((PrimaryDeviationCertificate.certificate_norm security order horder).trans
    (div_le_self (by norm_num) (one_le_pow₀ hb)))
open _root_.P2M7374ab17 renaming h257 → _p2mH257
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h255 (security order : ℕ) (horder : 1 ≤ order) :
    ∀ arity colors centers,
      |data security order (freeCertificate security order horder) arity colors centers| ≤ freeBound security order := by
  have hb : (1:ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  exact _p2mH102 security order _ 84 ((freeCertificate_norm_decay security order horder).trans
    (div_le_self (by norm_num) (one_le_pow₀ hb)))
open _root_.P2M7374ab17 renaming h255 → _p2mH255
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h253 (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    data security order (PairQuadraticFamilies.markedPairCertificate security order horder scalar) =
      data security order (MarkedPairCertificates.markedMixedCertificate security order horder scalar)+
      data security order (familyProduct (ProposalPrimary.primaryLaw security) (bodyReference security) order
        (PrimaryDeviationCertificate.certificate security order (by omega)) (freeCertificate security order (by omega))) := rfl
open _root_.P2M7374ab17 renaming h253 → _p2mH253
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h256 (security bits order : ℕ) (scalar : ℤ) :
    interpret security order (current security bits order scalar) =
      interpret security order (RationalMarkedCertificateProgram.current security bits order scalar)+
      interpret security order (RationalFamilyProductProgram.product order
        (RationalPrimaryDeviationProgram.current security bits order) (RationalBackgroundProgram.free security bits order)) := by
  funext arity colors centers
  exact Rat.cast_add _ _
open _root_.P2M7374ab17 renaming h256 → _p2mH256
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h254 (security order : ℕ) : 0 ≤ errorConstant security order := by
  have hm := _p2mH251 security
  have hp := _p2mH303 security
  rcases _p2mH147 security with ⟨hfree, _, hbody⟩
  have hf : 0 ≤ RationalBackgroundProgram.freeErrorConstant security := by
    unfold RationalBackgroundProgram.freeErrorConstant
    positivity
  have hprod := _p2mH103 order (primaryBound security order) (freeBound security order)
    _ _ (by unfold primaryBound coordinateFactor; positivity) (by unfold freeBound coordinateFactor; positivity) hp hf
  exact add_nonneg hm hprod
open _root_.P2M7374ab17 renaming h254 → _p2mH254
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h252 (security bits order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order scalar.val arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (PairQuadraticFamilies.markedPairCertificate security order horder scalar arity).val colors centers| ≤
      errorConstant security order*(1/(2:ℝ)^bits) := by
  have hp := _p2mH303 security
  rcases _p2mH147 security with ⟨hfree, _, hbody⟩
  have hf : 0 ≤ RationalBackgroundProgram.freeErrorConstant security := by
    unfold RationalBackgroundProgram.freeErrorConstant
    positivity
  have hprod := _p2mH104 security bits order
    (PrimaryDeviationCertificate.certificate security order (by omega)) (freeCertificate security order (by omega))
    (RationalPrimaryDeviationProgram.current security bits order) (RationalBackgroundProgram.free security bits order)
    (primaryBound security order) (freeBound security order)
    (RationalPrimaryDeviationProgram.errorConstant security) (RationalBackgroundProgram.freeErrorConstant security)
    (by unfold primaryBound coordinateFactor; positivity) (by unfold freeBound coordinateFactor; positivity) hp hf
    (_p2mH257 security order (by omega)) (_p2mH255 security order (by omega))
    (_p2mH301 security bits order (by omega) hfirst hprecision hbudget)
    (_p2mH149 security bits order (by omega) hfirst hprecision hbudget) arity colors centers
  have hm := _p2mH249 security bits order horder scalar hfirst hprecision hbudget arity colors centers
  change |interpret security order (current security bits order scalar.val) arity colors centers-
    data security order (PairQuadraticFamilies.markedPairCertificate security order horder scalar) arity colors centers| ≤ _
  rw [_p2mH256, _p2mH253]
  simp only [Pi.add_apply]
  have hid (a b c d : ℝ) : a+b-(c+d)=(a-c)+(b-d) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add hm hprod).trans_eq (by unfold errorConstant; ring))
open _root_.P2M7374ab17 renaming h252 → _p2mH252
end
open _root_.P2M7374ab17 renaming h252 → _p2mH252
open _root_.P2M7374ab17 renaming h253 → _p2mH253
open _root_.P2M7374ab17 renaming h254 → _p2mH254
open _root_.P2M7374ab17 renaming h255 → _p2mH255
open _root_.P2M7374ab17 renaming h256 → _p2mH256
open _root_.P2M7374ab17 renaming h257 → _p2mH257
end CurrentAFT.RationalMarkedPairProgram
open _root_.P2M7374ab17 renaming h252 → _p2mH252
open _root_.P2M7374ab17 renaming h253 → _p2mH253
open _root_.P2M7374ab17 renaming h254 → _p2mH254
open _root_.P2M7374ab17 renaming h255 → _p2mH255
open _root_.P2M7374ab17 renaming h256 → _p2mH256
open _root_.P2M7374ab17 renaming h257 → _p2mH257
end
open _root_.P2M7374ab17 renaming h253 → _p2mH253
open _root_.P2M7374ab17 renaming h255 → _p2mH255
open _root_.P2M7374ab17 renaming h254 → _p2mH254
open _root_.P2M7374ab17 renaming h256 → _p2mH256
open _root_.P2M7374ab17 renaming h257 → _p2mH257
open _root_.P2M7374ab17 renaming h252 → _p2mH252
section
namespace CurrentAFT.RationalDiffuseResidualProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls
  DiffusePair DiffusePairBounds DiffusePairResidual DiffusePairResidualRates
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff Parameters.safeMargin
  PublicParameterProgram.modulus primaryLaw centerLaw
attribute [local irreducible] pair seed smoothedSeed
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h179 (security colors width cutoff bits : ℕ) (scalar : ℤ) (first second : ℕ) :
    evaluate security colors width cutoff bits scalar first second =
      ∑ sign : Bool, ∑ left : Window cutoff, ∑ right : Window cutoff,
        (1 / 2 : ℚ) * RationalProposalProgram.gaussianWeight security cutoff bits left *
          RationalProposalProgram.gaussianWeight security cutoff bits right *
          AFT.V7Calibration.averagedPairProgram colors 1
            ((if sign then (width : ℤ) else -2 * (width : ℤ) + 1) + (left.val-right.val))
            scalar width first second := by
  unfold evaluate
  apply Finset.sum_congr rfl
  intro sign _
  let term (left right : Window cutoff) : ℚ :=
    (1 / 2 : ℚ) * RationalProposalProgram.gaussianWeight security cutoff bits left *
      RationalProposalProgram.gaussianWeight security cutoff bits right *
      AFT.V7Calibration.averagedPairProgram colors 1
        ((if sign then (width : ℤ) else -2 * (width : ℤ) + 1) + (left.val-right.val)) scalar width first second
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
open _root_.P2M7374ab17 renaming h179 → _p2mH179
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h178 (security colors width cutoff bits : ℕ) (scalar : ℤ) (first second : Fin colors) :
    (evaluate security colors width cutoff bits scalar first.val second.val : ℝ) =
      ((FiniteDist.uniform Bool).prod
        ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits).prod
          (windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits))).expectation
        (fun sample => AFT.TrimmedSlice.averagedPair colors 1
          ((if sample.1 then (width : ℤ) else -2 * (width : ℤ) + 1) + (sample.2.1.val - sample.2.2.val))
          scalar width first second) := by
  simp only [_p2mH179, Rat.cast_sum, Rat.cast_mul, Rat.cast_inv, Rat.cast_ofNat,
    RationalProposalProgram.gaussianWeight_eq, _p2mH24,
    FiniteDist.expectation, FiniteDist.prod_weight, Fintype.sum_prod_type, FiniteDist.uniform_weight,
    Fintype.card_bool, Nat.cast_ofNat, windowApproxLaw, one_div, mul_assoc]
open _root_.P2M7374ab17 renaming h178 → _p2mH178
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h182 (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    (pair security bits scalar first.val second.val : ℝ) =
      (approximatePairSeed security bits).expectation (pairTest security scalar first second) := by
  unfold pair
  have hcut : ((security + 2)^2 - 1) / 2 = edgeCutoff security := by
    simp only [edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  rw [hcut, PublicParameterProgram.modulus_value]
  have hw : (security + 2)^48 = Parameters.anchorWidth security := by
    simp only [Parameters.anchorWidth, Parameters.scale, Parameters.base, ← pow_mul]
  rw [hw, _p2mH178]
  rfl
open _root_.P2M7374ab17 renaming h182 → _p2mH182
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h180 (security : ℕ) (scalar : ℤ) (first second : Palette security) (sample : PairSeed security) :
    |pairTest security scalar first second sample| ≤ 1 := by
  rw [pairTest, ← _p2mH24]
  exact _p2mH23 _ _ _ _ _ _ _
open _root_.P2M7374ab17 renaming h180 → _p2mH180
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h181 (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(pair security bits scalar first.val second.val : ℝ)| ≤ 1 := by
  rw [_p2mH182]
  exact _p2mH42 _ _ 1 (_p2mH180 security scalar first second)
open _root_.P2M7374ab17 renaming h181 → _p2mH181
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h183 (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(pair security bits scalar first.val second.val : ℝ) - pairProfile security scalar first second| ≤ 2 / (2 : ℝ)^bits := by
  have hsingle : (∑ point, |(windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits).weight point -
      (edgeLaw security).weight point|) ≤ 1 / (2 : ℝ)^bits :=
    _p2mH16 _ _ _ _ (_p2mH327 security)
      (_p2mH328 security).symm
  have hpair := FiniteDist.l1_prod_le
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits) (edgeLaw security)
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits) (edgeLaw security)
  have hprod := FiniteDist.l1_prod_le (FiniteDist.uniform Bool) (FiniteDist.uniform Bool)
    ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits).prod
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits))
    ((edgeLaw security).prod (edgeLaw security))
  have hl1 : (∑ sample, |(approximatePairSeed security bits).weight sample - (pairSeedLaw security).weight sample|) ≤
      2 / (2 : ℝ)^bits := by
    unfold pairSeedLaw
    rw [_p2mH85]
    change (∑ sample, |((FiniteDist.uniform Bool).prod _).weight sample - ((FiniteDist.uniform Bool).prod _).weight sample|) ≤ _
    simp only [sub_self, abs_zero, Finset.sum_const_zero, zero_add] at hprod
    exact hprod.trans ((hpair.trans (add_le_add hsingle hsingle)).trans_eq (by ring))
  rw [_p2mH182]
  change |(approximatePairSeed security bits).expectation (pairTest security scalar first second) -
    (pairSeedLaw security).expectation (pairTest security scalar first second)| ≤ _
  exact (_p2mH47 _ _ _ 1
    (_p2mH180 security scalar first second)).trans (by simpa only [one_mul] using hl1)
open _root_.P2M7374ab17 renaming h183 → _p2mH183
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h186 (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    (seed security bits scalar first.val second.val : ℝ) =
      SafePair.coreSeed (safeCore security)
        (fun first second : Palette security => (pair security bits scalar first.val second.val : ℝ)) first second := by
  rw [seed, PublicParameterProgram.modulus_value, _p2mH13, _p2mH14]
  have href (color : Palette security) : (RationalBackgroundProfiles.safe security color.val : ℝ) =
      uniformFiniteProfile (safeCore security) color := by
    rw [_p2mH141]
    simp only [uniformFiniteProfile, safeCore_mem, safeCore_card, safeLaw_weight, safeHeight, one_div]
  simp only [href]
  unfold SafePair.coreSeed
  congr 1
  funext left right
  simp only [apply_ite, Rat.cast_zero, _p2mH142, SafePair.restrictPair, safeCore_mem]
  split_ifs <;> rfl
open _root_.P2M7374ab17 renaming h186 → _p2mH186
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h185 (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(seed security bits scalar first.val second.val : ℝ)| ≤ pairBound security := by
  rw [_p2mH186]
  unfold SafePair.coreSeed
  have hm (left right : Palette security) :
      |SafePair.restrictPair (safeCore security) (fun first second => (pair security bits scalar first.val second.val : ℝ)) left right| ≤ 1 := by
    unfold SafePair.restrictPair
    split_ifs
    · exact _p2mH181 security bits scalar left right
    · norm_num
  simpa only [Fintype.card_fin, mul_one, pairBound] using
    _p2mH2 (uniformFiniteProfile (safeCore security)) _ 1 (by norm_num)
      (_p2mH15 _) hm first second
open _root_.P2M7374ab17 renaming h185 → _p2mH185
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h187 (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(seed security bits scalar first.val second.val : ℝ) - safePairProfile security scalar first second| ≤
      2 * pairBound security * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH186]
  have hdiff : SafePair.coreSeed (safeCore security)
      (fun first second : Palette security => (pair security bits scalar first.val second.val : ℝ)) first second -
        safePairProfile security scalar first second =
      SafePair.canonicalPair (uniformFiniteProfile (safeCore security))
        (fun first second => SafePair.restrictPair (safeCore security)
          (fun first second => (pair security bits scalar first.val second.val : ℝ)) first second -
          SafePair.restrictPair (safeCore security) (pairProfile security scalar) first second) first second := by
    rw [_p2mH3]
    rfl
  rw [hdiff]
  have h := _p2mH2 (uniformFiniteProfile (safeCore security))
    (fun first second => SafePair.restrictPair (safeCore security)
      (fun first second => (pair security bits scalar first.val second.val : ℝ)) first second -
      SafePair.restrictPair (safeCore security) (pairProfile security scalar) first second)
    (2 / (2 : ℝ)^bits) (by positivity)
    (_p2mH15 _)
    (fun first second => by
      try dsimp only
      simp only [SafePair.restrictPair]
      split_ifs
      · exact _p2mH183 security bits scalar first second
      · simp only [sub_self, abs_zero]; positivity) first second
  exact h.trans_eq (by simp only [Fintype.card_fin, pairBound]; ring)
open _root_.P2M7374ab17 renaming h187 → _p2mH187
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h191 (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    (uniformCanonical security bits scalar first.val second.val : ℝ) =
      SafePair.canonicalPair (fun _ => 1 / (Parameters.modulus security : ℝ))
        (fun first second : Palette security => (pair security bits scalar first.val second.val : ℝ)) first second := by
  unfold uniformCanonical
  rw [PublicParameterProgram.modulus_value, _p2mH13, _p2mH14]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
open _root_.P2M7374ab17 renaming h191 → _p2mH191
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h192 (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(uniformCanonical security bits scalar first.val second.val : ℝ) -
      SafePair.canonicalPair (fun _ => 1 / (Parameters.modulus security : ℝ)) (pairProfile security scalar) first second| ≤
      2 * pairBound security * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH191, ← _p2mH3]
  have hq : 1 ≤ (Parameters.modulus security : ℝ) := by exact_mod_cast (Parameters.modulus_spec security).2.pos
  have href (color : Palette security) : |(1 : ℝ) / Parameters.modulus security| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hq
  exact (_p2mH2 _ _ (2 / (2 : ℝ)^bits) (by positivity) href
    (_p2mH183 security bits scalar) first second).trans_eq (by simp only [Fintype.card_fin, pairBound]; ring)
open _root_.P2M7374ab17 renaming h192 → _p2mH192
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h189 (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    (smoothedSeed security bits scalar first.val second.val : ℝ) =
      (RationalProposalProgram.approximateSeedLaw security bits).expectation (fun left =>
        (RationalProposalProgram.approximateSeedLaw security bits).expectation (fun right =>
          (seed security bits scalar
            (((shiftEquiv security (actualBlur security left)).symm first).val)
            (((shiftEquiv security (actualBlur security right)).symm second).val) : ℝ))) := by
  rw [smoothedSeed, _p2mH134]
  apply congrArg (FiniteDist.expectation _)
  funext left
  exact _p2mH134 security bits _ second
open _root_.P2M7374ab17 renaming h189 → _p2mH189
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h188 (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(smoothedSeed security bits scalar first.val second.val : ℝ)| ≤ pairBound security := by
  rw [_p2mH189]
  exact _p2mH42 _ _ _ (fun left =>
    _p2mH42 _ _ _ (fun right => _p2mH185 security bits scalar _ _))
open _root_.P2M7374ab17 renaming h188 → _p2mH188
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h190 (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(smoothedSeed security bits scalar first.val second.val : ℝ) -
      MarkedPairLeading.bodyConvolution security (fun left =>
        MarkedPairLeading.bodyConvolution security (safePairProfile security scalar left) second) first| ≤
      8 * pairBound security * (1 / (2 : ℝ)^bits) := by
  let B := pairBound security
  have hB : 0 ≤ B := by unfold B pairBound; positivity
  have hinner (left : Palette security) :
      |(RationalBackgroundProfiles.convolution security bits (seed security bits scalar left.val) second.val : ℝ) -
        BackgroundCertificates.rootConvolutionProfile security (safePairProfile security scalar left) second| ≤
        5 * B * (1 / (2 : ℝ)^bits) := by
    exact (_p2mH136 security bits (seed security bits scalar left.val)
      (safePairProfile security scalar left) B (2 * B * (1 / (2 : ℝ)^bits))
      (_p2mH185 security bits scalar left) (_p2mH187 security bits scalar left) second).trans_eq (by ring)
  have hbound (left : Palette security) :
      |(RationalBackgroundProfiles.convolution security bits (seed security bits scalar left.val) second.val : ℝ)| ≤ B := by
    rw [_p2mH134]
    exact _p2mH42 _ _ B (fun seed => _p2mH185 security bits scalar left _)
  unfold smoothedSeed
  change |(RationalBackgroundProfiles.convolution security bits
    (fun left => RationalBackgroundProfiles.convolution security bits (seed security bits scalar left) second.val) first.val : ℝ) -
      BackgroundCertificates.rootConvolutionProfile security (fun left =>
        BackgroundCertificates.rootConvolutionProfile security (safePairProfile security scalar left) second) first| ≤ _
  exact (_p2mH136 security bits
    (fun left => RationalBackgroundProfiles.convolution security bits (seed security bits scalar left) second.val)
    (fun left => BackgroundCertificates.rootConvolutionProfile security (safePairProfile security scalar left) second)
    B (5 * B * (1 / (2 : ℝ)^bits)) hbound hinner first).trans_eq (by ring)
open _root_.P2M7374ab17 renaming h190 → _p2mH190
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h184 (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(residual security bits scalar first.val second.val : ℝ) - finiteResidual security scalar first second| ≤
      10 * pairBound security * (1 / (2 : ℝ)^bits) := by
  have hideal : finiteResidual security scalar first second =
      SafePair.canonicalPair (fun _ => 1 / (Parameters.modulus security : ℝ)) (pairProfile security scalar) first second -
        MarkedPairLeading.bodyConvolution security (fun left =>
          MarkedPairLeading.bodyConvolution security (safePairProfile security scalar left) second) first := by
    change pullbackPair (Parameters.modulus security)
      (SafeConvolution.uniformCanonical (originalProfile security scalar)) first second -
      pullbackPair (Parameters.modulus security)
        (SafeConvolution.convolution (rootResiduePairLaw security).weight (seedProfile security scalar)) first second = _
    rw [← _p2mH50]
    congr 1
    exact congrFun (congrFun (_p2mH54 _ (pairProfile security scalar)) first) second
  rw [residual, Rat.cast_sub, hideal]
  have heq : (uniformCanonical security bits scalar first.val second.val : ℝ) -
      (smoothedSeed security bits scalar first.val second.val : ℝ) -
      (SafePair.canonicalPair (fun _ => 1 / (Parameters.modulus security : ℝ)) (pairProfile security scalar) first second -
        MarkedPairLeading.bodyConvolution security (fun left =>
          MarkedPairLeading.bodyConvolution security (safePairProfile security scalar left) second) first) =
      ((uniformCanonical security bits scalar first.val second.val : ℝ) -
        SafePair.canonicalPair (fun _ => 1 / (Parameters.modulus security : ℝ)) (pairProfile security scalar) first second) -
      ((smoothedSeed security bits scalar first.val second.val : ℝ) -
        MarkedPairLeading.bodyConvolution security (fun left =>
          MarkedPairLeading.bodyConvolution security (safePairProfile security scalar left) second) first) := by ring
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add (_p2mH192 security bits scalar first second)
    (_p2mH190 security bits scalar first second)).trans_eq (by ring))
open _root_.P2M7374ab17 renaming h184 → _p2mH184
end
open _root_.P2M7374ab17 renaming h178 → _p2mH178
open _root_.P2M7374ab17 renaming h179 → _p2mH179
open _root_.P2M7374ab17 renaming h180 → _p2mH180
open _root_.P2M7374ab17 renaming h181 → _p2mH181
open _root_.P2M7374ab17 renaming h182 → _p2mH182
open _root_.P2M7374ab17 renaming h183 → _p2mH183
open _root_.P2M7374ab17 renaming h184 → _p2mH184
open _root_.P2M7374ab17 renaming h185 → _p2mH185
open _root_.P2M7374ab17 renaming h186 → _p2mH186
open _root_.P2M7374ab17 renaming h187 → _p2mH187
open _root_.P2M7374ab17 renaming h188 → _p2mH188
open _root_.P2M7374ab17 renaming h189 → _p2mH189
open _root_.P2M7374ab17 renaming h190 → _p2mH190
open _root_.P2M7374ab17 renaming h191 → _p2mH191
open _root_.P2M7374ab17 renaming h192 → _p2mH192
end CurrentAFT.RationalDiffuseResidualProgram
open _root_.P2M7374ab17 renaming h178 → _p2mH178
open _root_.P2M7374ab17 renaming h179 → _p2mH179
open _root_.P2M7374ab17 renaming h180 → _p2mH180
open _root_.P2M7374ab17 renaming h181 → _p2mH181
open _root_.P2M7374ab17 renaming h182 → _p2mH182
open _root_.P2M7374ab17 renaming h183 → _p2mH183
open _root_.P2M7374ab17 renaming h184 → _p2mH184
open _root_.P2M7374ab17 renaming h185 → _p2mH185
open _root_.P2M7374ab17 renaming h186 → _p2mH186
open _root_.P2M7374ab17 renaming h187 → _p2mH187
open _root_.P2M7374ab17 renaming h188 → _p2mH188
open _root_.P2M7374ab17 renaming h189 → _p2mH189
open _root_.P2M7374ab17 renaming h190 → _p2mH190
open _root_.P2M7374ab17 renaming h191 → _p2mH191
open _root_.P2M7374ab17 renaming h192 → _p2mH192
end
open _root_.P2M7374ab17 renaming h188 → _p2mH188
open _root_.P2M7374ab17 renaming h178 → _p2mH178
open _root_.P2M7374ab17 renaming h181 → _p2mH181
open _root_.P2M7374ab17 renaming h186 → _p2mH186
open _root_.P2M7374ab17 renaming h180 → _p2mH180
open _root_.P2M7374ab17 renaming h190 → _p2mH190
open _root_.P2M7374ab17 renaming h179 → _p2mH179
open _root_.P2M7374ab17 renaming h182 → _p2mH182
open _root_.P2M7374ab17 renaming h185 → _p2mH185
open _root_.P2M7374ab17 renaming h184 → _p2mH184
open _root_.P2M7374ab17 renaming h191 → _p2mH191
open _root_.P2M7374ab17 renaming h192 → _p2mH192
open _root_.P2M7374ab17 renaming h183 → _p2mH183
open _root_.P2M7374ab17 renaming h187 → _p2mH187
open _root_.P2M7374ab17 renaming h189 → _p2mH189
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
theorem _root_.P2M7374ab17.h170 (security : ℕ) (scalar : ℤ) (first second : Palette security) :
    |pairProfile security scalar first second| ≤ 1 := by
  change |(pairSeedLaw security).expectation (pairTest security scalar first second)| ≤ 1
  exact _p2mH42 _ _ _ (_p2mH180 security scalar first second)
open _root_.P2M7374ab17 renaming h170 → _p2mH170
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h171 (security : ℕ) (scalar : ℤ) (first second : Palette security) :
    |safePairProfile security scalar first second| ≤ pairBound security := by
  unfold safePairProfile SafePair.coreSeed
  have hm (left right : Palette security) : |SafePair.restrictPair (safeCore security) (pairProfile security scalar) left right| ≤ 1 := by
    simp only [SafePair.restrictPair]
    split_ifs
    · exact _p2mH170 security scalar left right
    · norm_num
  simpa only [Fintype.card_fin, mul_one, pairBound] using
    _p2mH2 (uniformFiniteProfile (safeCore security)) _ 1 (by norm_num)
      (_p2mH15 _) hm first second
open _root_.P2M7374ab17 renaming h171 → _p2mH171
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h169 (security bits : ℕ) (color : Palette security) :
    |(RationalProposalProgram.center security bits color.val : ℝ)| ≤ 1 := by
  change |(RationalProposalProgram.approximateCenterLaw security bits).weight color| ≤ 1
  rw [abs_of_nonneg ((RationalProposalProgram.approximateCenterLaw security bits).nonneg color)]
  exact (RationalProposalProgram.approximateCenterLaw security bits).atom_le_one color
open _root_.P2M7374ab17 renaming h169 → _p2mH169
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h168 (security bits : ℕ) (scalar : ℤ) (first second : SafePalette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(bodyDensity security bits scalar first.val.val second.val.val : ℝ) - bodyPairDensity security scalar first second| ≤
      bodyErrorConstant security * (1 / (2 : ℝ)^bits) := by
  let q : ℝ := Parameters.modulus security
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let B := pairBound security
  let C := RationalBackgroundDensities.centerErrorConstant security
  let lower : ℝ := 1 / (4 * q^2)
  have hq : 0 < q := FirstResponse.modulus_pos security
  have hB : 0 ≤ B := by unfold B pairBound; positivity
  have hC : 0 ≤ C := by unfold C RationalBackgroundDensities.centerErrorConstant; positivity
  have he : 0 ≤ epsilon := by positivity
  have hqcenter (color : SafePalette security) :
      |(RationalProposalProgram.center security bits color.val.val : ℝ) - (bodyReference security).weight color| ≤ C * epsilon := by
    simpa only [C, epsilon, bodyReference, supportedLaw, centerLaw, RationalBackgroundDensities.centerErrorConstant] using
      _p2mH309 security bits color.val hprecision hbudget
  have hactual (color : SafePalette security) : |(bodyReference security).weight color| ≤ 1 := by
    rw [abs_of_nonneg ((bodyReference security).nonneg color)]
    exact (bodyReference security).atom_le_one color
  have hd : |(RationalProposalProgram.center security bits first.val.val : ℝ) *
      (RationalProposalProgram.center security bits second.val.val : ℝ) -
      (bodyReference security).weight first * (bodyReference security).weight second| ≤ 2 * C * epsilon := by
    calc
      _ = |((RationalProposalProgram.center security bits first.val.val : ℝ) - (bodyReference security).weight first) *
          (RationalProposalProgram.center security bits second.val.val : ℝ) + (bodyReference security).weight first *
          ((RationalProposalProgram.center security bits second.val.val : ℝ) - (bodyReference security).weight second)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ (C * epsilon) * 1 + 1 * (C * epsilon) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul (hqcenter first) (_p2mH169 security bits second.val) (abs_nonneg _) (by positivity))
          (mul_le_mul (hactual first) (hqcenter second) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have hlowQ : lower ≤ (RationalProposalProgram.center security bits first.val.val : ℝ) *
      (RationalProposalProgram.center security bits second.val.val : ℝ) := by
    calc
      _ = (1 / (2*q)) * (1 / (2*q)) := by dsimp only [lower]; field_simp; ring
      _ ≤ _ := mul_le_mul (_p2mH310 security bits first)
        (_p2mH310 security bits second) (by positivity)
        ((by positivity : (0 : ℝ) ≤ 1 / (2*q)).trans (_p2mH310 security bits first))
  have hlow : lower ≤ (bodyReference security).weight first * (bodyReference security).weight second := by
    calc
      _ = (1 / (2*q)) * (1 / (2*q)) := by dsimp only [lower]; field_simp; ring
      _ ≤ _ := mul_le_mul (bodyReference_lower security first) (bodyReference_lower security second)
        (by positivity) ((bodyReference security).nonneg first)
  have h := _p2mH167
    (seed security bits scalar first.val.val second.val.val : ℝ) (safePairProfile security scalar first.val second.val)
    ((RationalProposalProgram.center security bits first.val.val : ℝ) * (RationalProposalProgram.center security bits second.val.val : ℝ))
    ((bodyReference security).weight first * (bodyReference security).weight second)
    lower (2 * B * epsilon) (2 * C * epsilon) B (by dsimp only [lower]; positivity) hlowQ hlow
    (by positivity) (by positivity) hB (_p2mH187 security bits scalar first.val second.val) hd
    (_p2mH171 security scalar first.val second.val)
  rw [bodyDensity, Rat.cast_div, Rat.cast_mul, bodyPairDensity]
  exact h.trans_eq (by unfold bodyErrorConstant; dsimp only [lower, q, B, C, epsilon]; ring_nf; simp only [inv_inv])
open _root_.P2M7374ab17 renaming h168 → _p2mH168
end
open _root_.P2M7374ab17 renaming h168 → _p2mH168
open _root_.P2M7374ab17 renaming h169 → _p2mH169
open _root_.P2M7374ab17 renaming h170 → _p2mH170
open _root_.P2M7374ab17 renaming h171 → _p2mH171
end CurrentAFT.RationalDiffuseCertificateProgram
open _root_.P2M7374ab17 renaming h168 → _p2mH168
open _root_.P2M7374ab17 renaming h169 → _p2mH169
open _root_.P2M7374ab17 renaming h170 → _p2mH170
open _root_.P2M7374ab17 renaming h171 → _p2mH171
end
open _root_.P2M7374ab17 renaming h169 → _p2mH169
open _root_.P2M7374ab17 renaming h171 → _p2mH171
open _root_.P2M7374ab17 renaming h170 → _p2mH170
open _root_.P2M7374ab17 renaming h168 → _p2mH168
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
theorem _root_.P2M7374ab17.h284 (security : ℕ) (source output : Palette security) :
    RationalMassLiftProgram.actual security (Pi.single source 1) output =
      PrimaryTensorInverse.densityInverse security (Pi.single source 1) output / (primaryLaw security).weight source := by
  have hprofile : RootTaggedLocal.profileDensity security (Pi.single source 1) =
      ((primaryLaw security).weight source)⁻¹ • (Pi.single source 1 : Palette security → ℝ) := by
    funext color
    simp only [RootTaggedLocal.profileDensity_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : color = source
    · subst color; simp
    · simp [h]
  rw [RationalMassLiftProgram.actual, LinearMap.comp_apply, hprofile, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
open _root_.P2M7374ab17 renaming h284 → _p2mH284
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h285 (security degree : ℕ) (profile : (Fin degree → Palette security) → ℝ)
    (output : Fin degree → Palette security) :
    PrimaryTensorInverse.massLift security degree profile output =
      ∑ source : Fin degree → Palette security,
        profile source * ∏ index, RationalMassLiftProgram.actual security (Pi.single (source index) 1) (output index) := by
  change TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security)
    (PrimaryTensorInverse.massDensity security degree profile) output = _
  rw [TensorChannel.apply_formula_instance]
  apply Finset.sum_congr rfl
  intro source _
  simp only [_p2mH284, Finset.prod_div_distrib, PrimaryTensorInverse.massDensity,
    PrimaryTensorInverse.referenceWeight]
  ring
open _root_.P2M7374ab17 renaming h285 → _p2mH285
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h286 (security bits degree : ℕ) (profile : (Fin degree → ℕ) → ℚ) (output : Fin degree → Palette security) :
    (current security bits degree profile (fun index => (output index).val) : ℝ) =
      ∑ source : Fin degree → Palette security,
        (profile (fun index => (source index).val) : ℝ) *
          ∏ index, (entry security bits (source index).val (output index).val : ℝ) := by
  unfold current
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_prod]
  apply Finset.sum_congr (by ext; simp)
  intro source _
  rfl
open _root_.P2M7374ab17 renaming h286 → _p2mH286
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h289 (security bits : ℕ) (source output : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(entry security bits source.val output.val : ℝ) - RationalMassLiftProgram.actual security (Pi.single source 1) output| ≤
      RationalMassLiftProgram.errorConstant security * (1 / (2 : ℝ)^bits) := by
  have h := _p2mH279 security bits
    (fun color => if color = source.val then 1 else 0) 1 (by norm_num)
    (by intro color; split_ifs <;> norm_num) hfirst hprecision hbudget output
  have hp : (fun color : Palette security => ((if color.val = source.val then 1 else 0 : ℚ) : ℝ)) = Pi.single source 1 := by
    funext color
    by_cases h : color = source
    · subst color; simp
    · have hv : color.val ≠ source.val := fun heq => h (Fin.ext heq)
      simp [h, hv]
  rw [hp] at h
  simpa only [entry, mul_one] using h
open _root_.P2M7374ab17 renaming h289 → _p2mH289
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h290 (security : ℕ) : 1 ≤ factorBound security := by
  unfold factorBound
  linarith [_p2mH324 security, _p2mH282 security]
open _root_.P2M7374ab17 renaming h290 → _p2mH290
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h288 (security bits : ℕ) (source output : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(entry security bits source.val output.val : ℝ)| ≤ factorBound security ∧
      |RationalMassLiftProgram.actual security (Pi.single source 1) output| ≤ factorBound security := by
  have hactual : |RationalMassLiftProgram.actual security (Pi.single source 1) output| ≤ RationalTensorInverseProgram.actualBound security := by
    simpa only [mul_one] using _p2mH274 security (Pi.single source 1) 1 (by norm_num)
      (by intro color; simp only [Pi.single_apply]; split_ifs <;> norm_num) output
  have herror : |(entry security bits source.val output.val : ℝ) - RationalMassLiftProgram.actual security (Pi.single source 1) output| ≤
      RationalMassLiftProgram.errorConstant security :=
    (_p2mH289 security bits source output hfirst hprecision hbudget).trans (by
      have hepsilon : 1 / (2 : ℝ)^bits ≤ 1 := by
        rw [one_div]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hepsilon
        (_p2mH282 security))
  have hq : |(entry security bits source.val output.val : ℝ)| ≤
      |(entry security bits source.val output.val : ℝ) - RationalMassLiftProgram.actual security (Pi.single source 1) output| +
      |RationalMassLiftProgram.actual security (Pi.single source 1) output| := by
    simpa only [sub_zero] using abs_sub_le (entry security bits source.val output.val : ℝ)
      (RationalMassLiftProgram.actual security (Pi.single source 1) output) 0
  unfold factorBound
  constructor <;> linarith [_p2mH324 security,
    _p2mH282 security]
open _root_.P2M7374ab17 renaming h288 → _p2mH288
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h287 (security bits degree : ℕ) (computed : (Fin degree → ℕ) → ℚ)
    (profile : (Fin degree → Palette security) → ℝ) (bound profileError : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ profileError)
    (hcomputed : ∀ source : Fin degree → Palette security, |(computed (fun index => (source index).val) : ℝ)| ≤ bound)
    (hdiff : ∀ source : Fin degree → Palette security,
      |(computed (fun index => (source index).val) : ℝ) - profile source| ≤ profileError * (1 / (2 : ℝ)^bits))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Fin degree → Palette security) :
    |(current security bits degree computed (fun index => (output index).val) : ℝ) -
      PrimaryTensorInverse.massLift security degree profile output| ≤
      errorConstant security degree bound profileError * (1 / (2 : ℝ)^bits) := by
  rw [_p2mH286, _p2mH285, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hfactor : 0 ≤ factorBound security := (by norm_num : (0 : ℝ) ≤ 1).trans (_p2mH290 security)
  have heps : 0 ≤ 1 / (2 : ℝ)^bits := by positivity
  have hmass := _p2mH282 security
  calc
    _ ≤ ∑ _source : Fin degree → Palette security,
        (bound * degree * RationalMassLiftProgram.errorConstant security + profileError) *
          (factorBound security)^degree * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro source _
      let first := fun index : Fin degree => (entry security bits (source index).val (output index).val : ℝ)
      let second := fun index : Fin degree => RationalMassLiftProgram.actual security (Pi.single (source index) 1) (output index)
      have hprod := _p2mH326 Finset.univ first second
        (factorBound security) (RationalMassLiftProgram.errorConstant security * (1 / (2 : ℝ)^bits))
        (_p2mH290 security) (by positivity)
        (fun index _ => (_p2mH288 security bits _ _ hfirst hprecision hbudget).1)
        (fun index _ => (_p2mH288 security bits _ _ hfirst hprecision hbudget).2)
        (fun index _ => _p2mH289 security bits _ _ hfirst hprecision hbudget)
      simp only [Finset.card_univ, Fintype.card_fin] at hprod
      have habs : |∏ index, second index| ≤ (factorBound security)^degree := by
        rw [Finset.abs_prod]
        exact (Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          (fun index _ => (_p2mH288 security bits _ _ hfirst hprecision hbudget).2)).trans_eq (by simp)
      calc
        _ = |(computed (fun index => (source index).val) : ℝ) * ((∏ index, first index) - ∏ index, second index) +
            ((computed (fun index => (source index).val) : ℝ) - profile source) * ∏ index, second index| := by
          congr 1
          dsimp only [first, second]
          ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ bound * ((degree : ℝ) * (RationalMassLiftProgram.errorConstant security * (1 / (2 : ℝ)^bits)) *
              (factorBound security)^degree) +
            (profileError * (1 / (2 : ℝ)^bits)) * (factorBound security)^degree := by
          simp only [abs_mul]
          exact add_le_add (mul_le_mul (hcomputed source) hprod (abs_nonneg _) hb)
            (mul_le_mul (hdiff source) habs (abs_nonneg _) (by positivity))
        _ = _ := by ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      unfold errorConstant
      push_cast
      ring
open _root_.P2M7374ab17 renaming h287 → _p2mH287
end
open _root_.P2M7374ab17 renaming h284 → _p2mH284
open _root_.P2M7374ab17 renaming h285 → _p2mH285
open _root_.P2M7374ab17 renaming h286 → _p2mH286
open _root_.P2M7374ab17 renaming h287 → _p2mH287
open _root_.P2M7374ab17 renaming h288 → _p2mH288
open _root_.P2M7374ab17 renaming h289 → _p2mH289
open _root_.P2M7374ab17 renaming h290 → _p2mH290
end CurrentAFT.RationalMassLiftTensorProgram
open _root_.P2M7374ab17 renaming h284 → _p2mH284
open _root_.P2M7374ab17 renaming h285 → _p2mH285
open _root_.P2M7374ab17 renaming h286 → _p2mH286
open _root_.P2M7374ab17 renaming h287 → _p2mH287
open _root_.P2M7374ab17 renaming h288 → _p2mH288
open _root_.P2M7374ab17 renaming h289 → _p2mH289
open _root_.P2M7374ab17 renaming h290 → _p2mH290
end
open _root_.P2M7374ab17 renaming h287 → _p2mH287
open _root_.P2M7374ab17 renaming h284 → _p2mH284
open _root_.P2M7374ab17 renaming h289 → _p2mH289
open _root_.P2M7374ab17 renaming h288 → _p2mH288
open _root_.P2M7374ab17 renaming h286 → _p2mH286
open _root_.P2M7374ab17 renaming h285 → _p2mH285
open _root_.P2M7374ab17 renaming h290 → _p2mH290
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
theorem _root_.P2M7374ab17.h175 (security order degree : ℕ) (hdegree : degree ≤ order)
    (profile : (Fin degree → Palette security) → ℝ) (hcentered : PrimaryTensorInverse.MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    primaryTable order degree (PrimaryTensorInverse.massLift security degree profile) =
      fun arity => (PrimaryMassFamilies.massCertificateFamily security order degree hdegree profile hcentered hsymmetric arity).val := by
  funext arity colors centers
  by_cases h : arity = PrimaryMassFamilies.primaryArity order degree hdegree
  · subst arity
    simp only [PrimaryMassFamilies.massCertificateFamily, Pi.single_eq_same]
    simp [primaryTable, PrimaryMassFamilies.primaryArity, PrimaryMassFamilies.massLiftKernel]
  · have hshape : ¬(degree = arity.val.1.val ∧ 0 = arity.val.2.val) := by
      rintro ⟨hfirst, hsecond⟩
      apply h
      apply Subtype.ext
      exact Prod.ext (Fin.ext hfirst.symm) (Fin.ext hsecond.symm)
    simp only [primaryTable, dif_neg hshape, PrimaryMassFamilies.massCertificateFamily,
      Pi.single_eq_of_ne h, Submodule.coe_zero, Pi.zero_apply]
open _root_.P2M7374ab17 renaming h175 → _p2mH175
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h172 (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    bodyTable order (DiffusePairBounds.bodyPairDensity security scalar) =
      fun arity => (PairCertificateFamilies.diffuseBodyCertificate security order horder scalar arity).val := by
  funext arity colors centers
  by_cases h : arity = PairCertificateFamilies.bodyPairArity order horder
  · subst arity
    simp only [PairCertificateFamilies.diffuseBodyCertificate, Pi.single_eq_same]
    rw [_p2mH77 _ _ _ _ _ (_p2mH48 security scalar)]
    rfl
  · have hshape : ¬(arity.val.1.val = 0 ∧ arity.val.2.val = 2) := by
      rintro ⟨hfirst, hsecond⟩
      apply h
      apply Subtype.ext
      exact Prod.ext (Fin.ext hfirst) (Fin.ext hsecond)
    simp only [bodyTable, dif_neg hshape, PairCertificateFamilies.diffuseBodyCertificate,
      Pi.single_eq_of_ne h, Submodule.coe_zero, Pi.zero_apply]
open _root_.P2M7374ab17 renaming h172 → _p2mH172
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h177 (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(residual security bits scalar first.val second.val : ℝ)| ≤ 2 * pairBound security := by
  rw [RationalDiffuseResidualProgram.residual, Rat.cast_sub]
  have hq : 1 ≤ (Parameters.modulus security : ℝ) := by exact_mod_cast (Parameters.modulus_spec security).2.pos
  have hu : |(uniformCanonical security bits scalar first.val second.val : ℝ)| ≤ pairBound security := by
    rw [_p2mH191]
    have href (color : Palette security) : |(1 : ℝ) / Parameters.modulus security| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hq
    simpa only [Fintype.card_fin, pairBound, mul_one] using
      _p2mH2 _ _ 1 (by norm_num) href (_p2mH181 security bits scalar) first second
  exact (abs_sub _ _).trans ((add_le_add hu (_p2mH188 security bits scalar first second)).trans_eq (by ring))
open _root_.P2M7374ab17 renaming h177 → _p2mH177
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h176 (security bits : ℕ) (scalar : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (word : Fin 2 → Palette security) :
    |(RationalMassLiftTensorProgram.current security bits 2
      (fun source => residual security bits scalar (source 0) (source 1)) (fun index => (word index).val) : ℝ) -
      PrimaryTensorInverse.massLift security 2 (DiffusePairCertificates.residualMass security scalar) word| ≤
      primaryErrorConstant security * (1 / (2 : ℝ)^bits) := by
  exact _p2mH287 security bits 2 _ _
    (2 * pairBound security) (10 * pairBound security) (by unfold pairBound; positivity) (by unfold pairBound; positivity)
    (fun source => _p2mH177 security bits scalar (source 0) (source 1))
    (fun source => _p2mH184 security bits scalar (source 0) (source 1)) hfirst hprecision hbudget word
open _root_.P2M7374ab17 renaming h176 → _p2mH176
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h174 (security : ℕ) : 0 ≤ errorConstant security := by
  have hm := _p2mH282 security
  have hf := _p2mH290 security
  unfold errorConstant RationalDiffuseCertificateProgram.bodyErrorConstant primaryErrorConstant
    RationalMassLiftTensorProgram.errorConstant pairBound RationalBackgroundDensities.centerErrorConstant
  positivity
open _root_.P2M7374ab17 renaming h174 → _p2mH174
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h173 (security bits order : ℕ) (horder : 2 ≤ order) (scalar : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (DiffusePairCertificates.diffuseCertificate security order horder scalar arity).val colors centers| ≤
      errorConstant security * (1 / (2 : ℝ)^bits) := by
  have hb : |(body security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (PairCertificateFamilies.diffuseBodyCertificate security order horder scalar arity).val colors centers| ≤
      RationalDiffuseCertificateProgram.bodyErrorConstant security * (1 / (2 : ℝ)^bits) := by
    rw [← congrFun (congrFun (congrFun (_p2mH172 security order horder scalar) arity) colors) centers]
    unfold body bodyTable
    split_ifs
    · exact _p2mH168 security bits scalar _ _ hprecision hbudget
    · simp only [Rat.cast_zero, sub_self, abs_zero]
      unfold RationalDiffuseCertificateProgram.bodyErrorConstant pairBound RationalBackgroundDensities.centerErrorConstant
      positivity
  have hp : |(primary security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (DiffusePairCertificates.diffusePrimaryCertificate security order horder scalar arity).val colors centers| ≤
      primaryErrorConstant security * (1 / (2 : ℝ)^bits) := by
    unfold DiffusePairCertificates.diffusePrimaryCertificate
    rw [← congrFun (congrFun (congrFun (_p2mH175 security order 2 horder
      (DiffusePairCertificates.residualMass security scalar) (DiffusePairCertificates.residualMass_centered security scalar)
      (DiffusePairCertificates.residualMass_symmetric security scalar)) arity) colors) centers]
    unfold primary primaryTable
    split_ifs
    · exact _p2mH176 security bits scalar hfirst hprecision hbudget _
    · simp only [Rat.cast_zero, sub_self, abs_zero]
      unfold primaryErrorConstant RationalMassLiftTensorProgram.errorConstant RationalMassLiftTensorProgram.factorBound
        RationalMassLiftProgram.errorConstant RationalTensorInverseProgram.actualBound RationalDensityInverseProgram.inverseBound
        RationalFirstResponseProgram.inverseErrorConstant pairBound
      positivity
  change |((body security bits order scalar arity _ _ + primary security bits order scalar arity _ _ : ℚ) : ℝ) -
    ((PairCertificateFamilies.diffuseBodyCertificate security order horder scalar arity).val colors centers +
      (DiffusePairCertificates.diffusePrimaryCertificate security order horder scalar arity).val colors centers)| ≤ _
  rw [Rat.cast_add]
  have hsplit : (body security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) +
      (primary security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      ((PairCertificateFamilies.diffuseBodyCertificate security order horder scalar arity).val colors centers +
        (DiffusePairCertificates.diffusePrimaryCertificate security order horder scalar arity).val colors centers) =
    ((body security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (PairCertificateFamilies.diffuseBodyCertificate security order horder scalar arity).val colors centers) +
    ((primary security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (DiffusePairCertificates.diffusePrimaryCertificate security order horder scalar arity).val colors centers) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans ((add_le_add hb hp).trans_eq (by unfold errorConstant; ring))
open _root_.P2M7374ab17 renaming h173 → _p2mH173
end
open _root_.P2M7374ab17 renaming h172 → _p2mH172
open _root_.P2M7374ab17 renaming h173 → _p2mH173
open _root_.P2M7374ab17 renaming h174 → _p2mH174
open _root_.P2M7374ab17 renaming h175 → _p2mH175
open _root_.P2M7374ab17 renaming h176 → _p2mH176
open _root_.P2M7374ab17 renaming h177 → _p2mH177
end CurrentAFT.RationalDiffuseFamilyProgram
open _root_.P2M7374ab17 renaming h172 → _p2mH172
open _root_.P2M7374ab17 renaming h173 → _p2mH173
open _root_.P2M7374ab17 renaming h174 → _p2mH174
open _root_.P2M7374ab17 renaming h175 → _p2mH175
open _root_.P2M7374ab17 renaming h176 → _p2mH176
open _root_.P2M7374ab17 renaming h177 → _p2mH177
end
open _root_.P2M7374ab17 renaming h174 → _p2mH174
open _root_.P2M7374ab17 renaming h177 → _p2mH177
open _root_.P2M7374ab17 renaming h176 → _p2mH176
open _root_.P2M7374ab17 renaming h172 → _p2mH172
open _root_.P2M7374ab17 renaming h175 → _p2mH175
open _root_.P2M7374ab17 renaming h173 → _p2mH173
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
theorem _root_.P2M7374ab17.h292 (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ∀ arity colors centers,
      |data security order (DiffusePairCertificates.diffuseCertificate security order horder scalar.val) arity colors centers| ≤ diffuseBound security order := by
  have hb : (1:ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  apply _p2mH102 security order _ 388480
  exact (DiffusePairCertificates.diffuseCertificate_norm security order horder scalar.val
    ((InwardAnchor.scalar_bound security scalar).trans (by omega))).trans (div_le_self (by norm_num) (one_le_pow₀ hb))
open _root_.P2M7374ab17 renaming h292 → _p2mH292
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h294 (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ∀ arity colors centers,
      |data security order (PairQuadraticFamilies.markedPairCertificate security order horder scalar) arity colors centers| ≤ markedBound security order := by
  have hb : (1:ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  exact _p2mH102 security order _ 18400 ((PairQuadraticFamilies.markedPairCertificate_norm security order horder scalar).trans
    (div_le_self (by norm_num) (one_le_pow₀ hb)))
open _root_.P2M7374ab17 renaming h294 → _p2mH294
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h293 (security order : ℕ) : 0 ≤ errorConstant security order := by
  have hm := _p2mH254 security order
  have hd := _p2mH174 security
  unfold errorConstant diffuseBound markedBound coordinateFactor
  positivity
open _root_.P2M7374ab17 renaming h293 → _p2mH293
set_option maxRecDepth 8192
private theorem _root_.P2M7374ab17.h334 (x y X Y a r ε e f A B : ℝ)
    (hε : 0 ≤ ε) (he : 0 ≤ e) (hf : 0 ≤ f) (_hA : 0 ≤ A) (_hB : 0 ≤ B)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : |x-X| ≤ e*ε) (hy : |y-Y| ≤ f*ε)
    (hX : |X| ≤ A) (hY : |Y| ≤ B) (hr : |a-r| ≤ (1/2:ℝ)*ε) :
    |(1-a)*x+a*y-((1-r)*X+r*Y)| ≤ (e+f+(A+B)/2)*ε := by
  have hrem : 0 ≤ 1-a := by linarith
  have hrem1 : 1-a ≤ 1 := by linarith
  have hgap : |Y-X| ≤ A+B := (abs_sub _ _).trans ((add_le_add hY hX).trans_eq (by ring))
  rw [show (1-a)*x+a*y-((1-r)*X+r*Y)=(1-a)*(x-X)+a*(y-Y)+(a-r)*(Y-X) by ring]
  calc
    _ ≤ |(1-a)*(x-X)|+|a*(y-Y)|+|(a-r)*(Y-X)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = (1-a)*|x-X|+a*|y-Y|+|a-r| * |Y-X| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hrem, abs_of_nonneg ha]
    _ ≤ e*ε+f*ε+((1/2:ℝ)*ε)*(A+B) := by
      apply add_le_add
      · exact add_le_add
          ((mul_le_mul_of_nonneg_left hx hrem).trans ((mul_le_mul_of_nonneg_right hrem1 (mul_nonneg he hε)).trans_eq (one_mul _)))
          ((mul_le_mul_of_nonneg_left hy ha).trans ((mul_le_mul_of_nonneg_right ha1 (mul_nonneg hf hε)).trans_eq (one_mul _)))
      · exact mul_le_mul hr hgap (abs_nonneg _) (by positivity)
    _ = _ := by ring
open _root_.P2M7374ab17 renaming h334 → _p2mH334
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h291 (security bits order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order scalar.val arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (PairQuadraticFamilies.pairQuadraticCertificate security order horder scalar arity).val colors centers| ≤
      errorConstant security order*(1/(2:ℝ)^bits) := by
  have hd := _p2mH173 security bits order horder scalar.val hfirst hprecision hbudget arity colors centers
  have hm := _p2mH252 security bits order horder scalar hfirst hprecision hbudget arity colors centers
  have ha := LocalPairProgram.activationApprox_bounds security bits
  have hrate := _p2mH75 security bits
  simp only [current, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one,
    PairQuadraticFamilies.pairQuadraticCertificate, Pi.add_apply, Pi.smul_apply,
    Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
  exact _p2mH334 _ _ _ _ _ _ _ _ _ _ _ (by positivity) (_p2mH174 security)
    (_p2mH254 security order)
    (by unfold diffuseBound coordinateFactor; positivity) (by unfold markedBound coordinateFactor; positivity)
    ha.1 (ha.2.trans (by norm_num)) hd hm (_p2mH292 security order horder scalar arity colors centers)
    (_p2mH294 security order horder scalar arity colors centers) hrate
open _root_.P2M7374ab17 renaming h291 → _p2mH291
end
open _root_.P2M7374ab17 renaming h291 → _p2mH291
open _root_.P2M7374ab17 renaming h292 → _p2mH292
open _root_.P2M7374ab17 renaming h293 → _p2mH293
open _root_.P2M7374ab17 renaming h294 → _p2mH294
open _root_.P2M7374ab17 renaming h334 → _p2mH334
end CurrentAFT.RationalPairQuadraticProgram
open _root_.P2M7374ab17 renaming h291 → _p2mH291
open _root_.P2M7374ab17 renaming h292 → _p2mH292
open _root_.P2M7374ab17 renaming h293 → _p2mH293
open _root_.P2M7374ab17 renaming h294 → _p2mH294
open _root_.P2M7374ab17 renaming h334 → _p2mH334
end
open _root_.P2M7374ab17 renaming h292 → _p2mH292
open _root_.P2M7374ab17 renaming h293 → _p2mH293
open _root_.P2M7374ab17 renaming h294 → _p2mH294
open _root_.P2M7374ab17 renaming h291 → _p2mH291
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
theorem _root_.P2M7374ab17.h155 (security : ℕ) (scalar : FirstHistogram.Scalar security) (primary output : FirstHistogram.Palette security) :
    |actualPairProfile security scalar primary output| ≤ 2 := by
  have hfirst := (ConditionalPairMean.firstMarginal (LocalReferenceEnergy.pairAt security primary scalar)).atom_le_one output
  have hsecond := (ConditionalPairMean.secondMarginal (LocalReferenceEnergy.pairAt security primary scalar)).atom_le_one output
  have hf0 := (ConditionalPairMean.firstMarginal (LocalReferenceEnergy.pairAt security primary scalar)).nonneg output
  have hs0 := (ConditionalPairMean.secondMarginal (LocalReferenceEnergy.pairAt security primary scalar)).nonneg output
  change |(ConditionalPairMean.firstMarginal (LocalReferenceEnergy.pairAt security primary scalar)).weight output+
    (ConditionalPairMean.secondMarginal (LocalReferenceEnergy.pairAt security primary scalar)).weight output| ≤ 2
  rw [abs_of_nonneg (add_nonneg hf0 hs0)]
  linarith
open _root_.P2M7374ab17 renaming h155 → _p2mH155
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h163 (security bits : ℕ) (scalar : FirstHistogram.Scalar security) (primary output : FirstHistogram.Palette security) :
    |(pairProfile security bits primary.val scalar.val output.val:ℝ)-actualPairProfile security scalar primary output| ≤
      6*(Parameters.modulus security:ℝ)*(1/(2:ℝ)^bits) := by
  unfold pairProfile
  rw [Rat.cast_add, Rat.cast_sum, Rat.cast_sum, colors, PublicParameterProgram.modulus_value]
  unfold actualPairProfile
  have hf : |(∑ other : FirstHistogram.Palette security, (LocalPairProgram.current security bits primary.val scalar.val output.val other.val:ℝ))-
      ∑ other : FirstHistogram.Palette security, (LocalReferenceEnergy.pairAt security primary scalar).weight (output, other)| ≤
      (Parameters.modulus security:ℝ)*(3/(2:ℝ)^bits) := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun other _ => _p2mH76 security bits primary output other scalar)).trans_eq (by simp))
  have hs : |(∑ other : FirstHistogram.Palette security, (LocalPairProgram.current security bits primary.val scalar.val other.val output.val:ℝ))-
      ∑ other : FirstHistogram.Palette security, (LocalReferenceEnergy.pairAt security primary scalar).weight (other, output)| ≤
      (Parameters.modulus security:ℝ)*(3/(2:ℝ)^bits) := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun other _ => _p2mH76 security bits primary other output scalar)).trans_eq (by simp))
  have hid (a b c d : ℝ) : a+b-(c+d)=(a-c)+(b-d) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add hf hs).trans_eq (by ring))
open _root_.P2M7374ab17 renaming h163 → _p2mH163
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h161 (security bits : ℕ) (scalar : FirstHistogram.Scalar security) (output : FirstHistogram.Palette security) :
    (pairMean security bits scalar.val output.val:ℝ) =
      (RationalProposalProgram.approximatePrimaryLaw security bits).expectation
        (fun primary => (pairProfile security bits primary.val scalar.val output.val:ℝ)) := by
  unfold pairMean
  rw [Rat.cast_sum, colors, PublicParameterProgram.modulus_value]
  simp only [FiniteDist.expectation, RationalProposalProgram.approximatePrimaryLaw, Rat.cast_mul]
open _root_.P2M7374ab17 renaming h161 → _p2mH161
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h162 (security bits : ℕ) (scalar : FirstHistogram.Scalar security) (output : FirstHistogram.Palette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(pairMean security bits scalar.val output.val:ℝ)-ConditionalPairMean.pairMean security scalar output| ≤
      profileErrorConstant security*(1/(2:ℝ)^bits) := by
  rw [_p2mH161, _p2mH45]
  have hx := _p2mH223 (primaryLaw security) (RationalProposalProgram.approximatePrimaryLaw security bits)
    (fun primary => actualPairProfile security scalar primary output)
    (fun primary => (pairProfile security bits primary.val scalar.val output.val:ℝ))
    (6*(Parameters.modulus security:ℝ)*(1/(2:ℝ)^bits))
    (64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits)) 2
    (by positivity) (by norm_num) (fun primary => _p2mH163 security bits scalar primary output)
    (fun primary => by simpa only [RationalProposalProgram.approximatePrimaryLaw, primaryLaw] using _p2mH318 security bits primary hprecision hbudget)
    (fun primary => _p2mH155 security scalar primary output)
  exact hx.trans_eq (by unfold profileErrorConstant; simp only [Fintype.card_fin]; ring)
open _root_.P2M7374ab17 renaming h162 → _p2mH162
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h157 (security bits : ℕ) (scalar : FirstHistogram.Scalar security) (output : FirstHistogram.Palette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(centeredMean security bits scalar.val output.val:ℝ)-ConditionalPairMean.centeredMean security scalar output| ≤
      profileErrorConstant security*(1/(2:ℝ)^bits) := by
  simp only [centeredMean, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, colors, PublicParameterProgram.modulus_value,
    ConditionalPairMean.centeredMean, FringeCertificate.uniformProfile]
  convert _p2mH162 security bits scalar output hprecision hbudget using 1
  congr 1
  ring
open _root_.P2M7374ab17 renaming h157 → _p2mH157
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h156 (security bits : ℕ) (scalar : FirstHistogram.Scalar security) (output : FirstHistogram.Palette security) :
    |(centeredMean security bits scalar.val output.val:ℝ)| ≤ computedBound security := by
  have heps : 1/(2:ℝ)^bits ≤ 1 := by
    exact (div_le_one (by positivity : (0:ℝ)<2^bits)).mpr (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hp (primary : FirstHistogram.Palette security) : |(pairProfile security bits primary.val scalar.val output.val:ℝ)| ≤ 2+6*(Parameters.modulus security:ℝ) := by
    have hx := _p2mH163 security bits scalar primary output
    have hy := _p2mH155 security scalar primary output
    have hz := abs_sub_le (pairProfile security bits primary.val scalar.val output.val:ℝ)
      (actualPairProfile security scalar primary output) 0
    simp only [sub_zero] at hz
    exact hz.trans ((add_le_add hx hy).trans (by nlinarith [mul_le_mul_of_nonneg_left heps (by positivity : (0:ℝ)≤6*Parameters.modulus security)]))
  have hm : |(pairMean security bits scalar.val output.val:ℝ)| ≤ 2+6*(Parameters.modulus security:ℝ) := by
    rw [_p2mH161]
    exact _p2mH42 _ _ _ hp
  have hq : (1:ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Nat.succ_le_of_lt (Parameters.modulus_spec security).2.pos)
  have hu : |2/(Parameters.modulus security:ℝ)| ≤ 2 := by
    rw [abs_of_nonneg (by positivity : (0:ℝ)≤2/(Parameters.modulus security:ℝ))]
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  simp only [centeredMean, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, colors, PublicParameterProgram.modulus_value]
  exact (abs_sub _ _).trans ((add_le_add hm hu).trans_eq (by unfold computedBound; ring))
open _root_.P2M7374ab17 renaming h156 → _p2mH156
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h159 (security order : ℕ) (horder : 1 ≤ order) (scalar : FirstHistogram.Scalar security) :
    RationalBackgroundTable.firstTable order (RationalMassLiftProgram.actual security (ConditionalPairMean.centeredMean security scalar))
      (fun _ : SafePalette security => (0:ℝ)) =
    fun arity => (ConditionalPairLinear.certificate security order horder scalar arity).val := by
  exact _p2mH273 security order horder (ConditionalPairMean.centeredMean security scalar)
    (ConditionalPairLinear.wordMean_centered security scalar) (ConditionalPairLinear.wordMean_symmetric security scalar)
open _root_.P2M7374ab17 renaming h159 → _p2mH159
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h160 (security : ℕ) : 0 ≤ errorConstant security := by
  simp only [errorConstant, computedBound, profileErrorConstant, RationalMassLiftProgram.errorConstant,
    RationalTensorInverseProgram.actualBound, RationalDensityInverseProgram.inverseBound, RationalFirstResponseProgram.inverseErrorConstant]
  positivity
open _root_.P2M7374ab17 renaming h160 → _p2mH160
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h158 (security bits order : ℕ) (horder : 1 ≤ order) (scalar : FirstHistogram.Scalar security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order scalar.val arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (ConditionalPairLinear.certificate security order horder scalar arity).val colors centers| ≤ errorConstant security*(1/(2:ℝ)^bits) := by
  have hl (primary : FirstHistogram.Palette security) :
      |(RationalMassLiftProgram.current security bits (centeredMean security bits scalar.val) primary.val:ℝ)-
        RationalMassLiftProgram.actual security (ConditionalPairMean.centeredMean security scalar) primary| ≤ errorConstant security*(1/(2:ℝ)^bits) := by
    exact (_p2mH280 security bits (centeredMean security bits scalar.val)
      (ConditionalPairMean.centeredMean security scalar) (computedBound security) (profileErrorConstant security*(1/(2:ℝ)^bits))
      (by unfold computedBound; positivity) (by unfold profileErrorConstant; positivity)
      (_p2mH156 security bits scalar) (fun output => _p2mH157 security bits scalar output hprecision hbudget)
      hfirst hprecision hbudget primary).trans_eq (by unfold errorConstant; ring)
  have hx := _p2mH153 order (RationalMassLiftProgram.current security bits (centeredMean security bits scalar.val)) (fun _ => 0)
    (RationalMassLiftProgram.actual security (ConditionalPairMean.centeredMean security scalar)) (fun _ : SafePalette security => 0)
    Fin.val (fun color => color.val.val) (errorConstant security*(1/(2:ℝ)^bits)) 0
    (mul_nonneg (_p2mH160 security) (by positivity)) (by norm_num) hl (fun _ => by norm_num) arity colors centers
  rw [_p2mH159 security order horder scalar] at hx
  simpa only [add_zero,current] using hx
open _root_.P2M7374ab17 renaming h158 → _p2mH158
end
open _root_.P2M7374ab17 renaming h155 → _p2mH155
open _root_.P2M7374ab17 renaming h156 → _p2mH156
open _root_.P2M7374ab17 renaming h157 → _p2mH157
open _root_.P2M7374ab17 renaming h158 → _p2mH158
open _root_.P2M7374ab17 renaming h159 → _p2mH159
open _root_.P2M7374ab17 renaming h160 → _p2mH160
open _root_.P2M7374ab17 renaming h161 → _p2mH161
open _root_.P2M7374ab17 renaming h162 → _p2mH162
open _root_.P2M7374ab17 renaming h163 → _p2mH163
end CurrentAFT.RationalConditionalPairProgram
open _root_.P2M7374ab17 renaming h155 → _p2mH155
open _root_.P2M7374ab17 renaming h156 → _p2mH156
open _root_.P2M7374ab17 renaming h157 → _p2mH157
open _root_.P2M7374ab17 renaming h158 → _p2mH158
open _root_.P2M7374ab17 renaming h159 → _p2mH159
open _root_.P2M7374ab17 renaming h160 → _p2mH160
open _root_.P2M7374ab17 renaming h161 → _p2mH161
open _root_.P2M7374ab17 renaming h162 → _p2mH162
open _root_.P2M7374ab17 renaming h163 → _p2mH163
end
open _root_.P2M7374ab17 renaming h163 → _p2mH163
open _root_.P2M7374ab17 renaming h156 → _p2mH156
open _root_.P2M7374ab17 renaming h162 → _p2mH162
open _root_.P2M7374ab17 renaming h155 → _p2mH155
open _root_.P2M7374ab17 renaming h160 → _p2mH160
open _root_.P2M7374ab17 renaming h159 → _p2mH159
open _root_.P2M7374ab17 renaming h157 → _p2mH157
open _root_.P2M7374ab17 renaming h158 → _p2mH158
open _root_.P2M7374ab17 renaming h161 → _p2mH161
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
theorem _root_.P2M7374ab17.h322 (security bits order : ℕ)
    (table : ℤ → RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → ℕ)
    (centers : Fin arity.val.2.val → ℕ) :
    current security bits order table arity colors centers =
      ∑ scalar : Window (RationalBackgroundLinearProgram.cutoff security),
        RationalProposalProgram.gaussianWeight security (RationalBackgroundLinearProgram.cutoff security) bits scalar*
          table scalar.val arity colors centers := by
  unfold current
  exact (FiniteConvolutionProgram.windowIndexEquiv (RationalBackgroundLinearProgram.cutoff security)).sum_comp
    (fun scalar : Window (RationalBackgroundLinearProgram.cutoff security) =>
      RationalProposalProgram.gaussianWeight security (RationalBackgroundLinearProgram.cutoff security) bits scalar*
        table scalar.val arity colors centers)
open _root_.P2M7374ab17 renaming h322 → _p2mH322
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h321 (security bits order : ℕ)
    (table : ℤ → RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    interpret security order (current security bits order table) arity colors centers =
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security-1) bits).expectation
        (fun scalar => interpret security order (table scalar.val) arity colors centers) := by
  change (current security bits order table arity (fun index => (colors index).val)
    (fun index => (centers index).val.val):ℝ) = _
  rw [_p2mH322]
  rw [Rat.cast_sum, _p2mH116]
  simp only [Rat.cast_mul, RationalProposalProgram.gaussianWeight_eq,
    FiniteDist.expectation, windowApproxLaw, interpret, RationalFamilyProductProgram.pullback,
    RationalFamilyProductProgram.realTable]
  rfl
open _root_.P2M7374ab17 renaming h321 → _p2mH321
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h320 (security order : ℕ)
    (families : MarkedPairSeed.Scalar security → ActualFamily security order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    data security order (actual security order families) arity colors centers =
      (scalarLaw security).expectation (fun scalar => data security order (families scalar) arity colors centers) := by
  simp only [actual, data, FiniteDist.expectation, Finset.sum_apply, Submodule.coe_sum,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
open _root_.P2M7374ab17 renaming h320 → _p2mH320
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h323 (security bits order : ℕ)
    (families : MarkedPairSeed.Scalar security → ActualFamily security order)
    (table : ℤ → RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (B e : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ scalar arity colors centers, |data security order (families scalar) arity colors centers| ≤ B)
    (herror : ∀ scalar arity colors centers,
      |interpret security order (table scalar.val) arity colors centers-
        data security order (families scalar) arity colors centers| ≤ e*(1/(2:ℝ)^bits))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (current security bits order table) arity colors centers-
      data security order (actual security order families) arity colors centers| ≤ (e+B)*(1/(2:ℝ)^bits) := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security-1) bits
  let computed := fun scalar : MarkedPairSeed.Scalar security => interpret security order (table scalar.val) arity colors centers
  let ideal := fun scalar : MarkedPairSeed.Scalar security => data security order (families scalar) arity colors centers
  have hpoint := _p2mH42 approximate
    (fun scalar => computed scalar-ideal scalar) (e*(1/(2:ℝ)^bits))
    (fun scalar => herror scalar arity colors centers)
  rw [FiniteDist.expectation_sub] at hpoint
  have hl1 := _p2mH16 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security-1) bits (_p2mH327 security)
    (_p2mH328 security).symm
  have hsource := (_p2mH47 approximate (scalarLaw security) ideal B
    (fun scalar => hbound scalar arity colors centers)).trans (mul_le_mul_of_nonneg_left hl1 hB)
  rw [_p2mH321, _p2mH320]
  exact (abs_sub_le _ (approximate.expectation ideal) _).trans
    ((add_le_add hpoint hsource).trans_eq (by ring))
open _root_.P2M7374ab17 renaming h323 → _p2mH323
end
open _root_.P2M7374ab17 renaming h320 → _p2mH320
open _root_.P2M7374ab17 renaming h321 → _p2mH321
open _root_.P2M7374ab17 renaming h322 → _p2mH322
open _root_.P2M7374ab17 renaming h323 → _p2mH323
end CurrentAFT.RationalScalarFamilyAverage
open _root_.P2M7374ab17 renaming h320 → _p2mH320
open _root_.P2M7374ab17 renaming h321 → _p2mH321
open _root_.P2M7374ab17 renaming h322 → _p2mH322
open _root_.P2M7374ab17 renaming h323 → _p2mH323
end
open _root_.P2M7374ab17 renaming h323 → _p2mH323
open _root_.P2M7374ab17 renaming h322 → _p2mH322
open _root_.P2M7374ab17 renaming h321 → _p2mH321
open _root_.P2M7374ab17 renaming h320 → _p2mH320
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
private theorem _root_.P2M7374ab17.h333 (security : ℕ) : (1:ℝ) ≤ Parameters.base security := by
  exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
open _root_.P2M7374ab17 renaming h333 → _p2mH333
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h239 (security order : ℕ) (horder : 1 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ∀ arity colors centers, |data security order (ConditionalPairLinear.certificate security order horder scalar) arity colors centers| ≤ conditionalLinearBound security order :=
  _p2mH102 security order _ 32768 ((ConditionalPairLinear.certificate_norm security order horder scalar).trans
    (div_le_self (by norm_num) (one_le_pow₀ (_p2mH333 security))))
open _root_.P2M7374ab17 renaming h239 → _p2mH239
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h245 (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ∀ arity colors centers, |data security order (PairQuadraticFamilies.pairQuadraticCertificate security order horder scalar) arity colors centers| ≤ pairBound security order :=
  _p2mH102 security order _ 406880 ((PairQuadraticFamilies.pairQuadraticCertificate_norm security order horder scalar).trans
    (div_le_self (by norm_num) (one_le_pow₀ (_p2mH333 security))))
open _root_.P2M7374ab17 renaming h245 → _p2mH245
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h246 (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ∀ arity colors centers, |data security order (LegBackgroundFamilies.conditionalQuadratic security order horder scalar) arity colors centers| ≤ quadraticBound security order :=
  _p2mH102 security order _ 2241888 ((LegBackgroundFamilies.conditionalQuadratic_norm security order horder scalar).trans
    (div_le_self (by norm_num) (one_le_pow₀ (_p2mH333 security))))
open _root_.P2M7374ab17 renaming h246 → _p2mH246
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h241 (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ∀ arity colors centers, |data security order (LegBackgroundFamilies.conditionalCubic security order horder scalar) arity colors centers| ≤ cubicBound security order :=
  _p2mH102 security order _ 22785280 ((LegBackgroundFamilies.conditionalCubic_norm security order horder scalar).trans
    (div_le_self (by norm_num) (one_le_pow₀ (_p2mH333 security))))
open _root_.P2M7374ab17 renaming h241 → _p2mH241
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h248 (security : ℕ) : 0 ≤ RationalBackgroundProgram.translationErrorConstant security := by
  rcases _p2mH147 security with ⟨hp, hr, hb⟩
  unfold RationalBackgroundProgram.translationErrorConstant
  positivity
open _root_.P2M7374ab17 renaming h248 → _p2mH248
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h244 (security order : ℕ) : 0 ≤ errorConstant security order := by
  have hp := _p2mH160 security
  have hpair := _p2mH293 security order
  have ht := _p2mH248 security
  rcases _p2mH147 security with ⟨hprimary, _, hbody⟩
  have hf : 0 ≤ RationalBackgroundProgram.freeErrorConstant security := by
    unfold RationalBackgroundProgram.freeErrorConstant
    positivity
  have hm : 0 ≤ RationalBackgroundLinearProgram.meanErrorConstant security order := by
    unfold RationalBackgroundLinearProgram.meanErrorConstant RationalBackgroundLinearProgram.translationBound
    positivity
  have hl : 0 ≤ RationalBackgroundLinearProgram.linearErrorConstant security order := by
    unfold RationalBackgroundLinearProgram.linearErrorConstant
    exact div_nonneg (add_nonneg (mul_nonneg (ProposalPrimary.freeMass_nonneg security) hf)
      (mul_nonneg (Nat.cast_nonneg _) hm)) (Nat.cast_nonneg _)
  have hprod1 := _p2mH103 order (conditionalLinearBound security order)
    (RationalBackgroundLinearProgram.translationBound security order) _ _
    (by unfold conditionalLinearBound coordinateFactor; positivity)
    (by unfold RationalBackgroundLinearProgram.translationBound; positivity) hp ht
  have hprod2 := _p2mH103 order (pairBound security order)
    (RationalBackgroundLinearProgram.translationBound security order) _ _
    (by unfold pairBound coordinateFactor; positivity)
    (by unfold RationalBackgroundLinearProgram.translationBound; positivity) hpair ht
  unfold errorConstant conditionalQuadraticError conditionalCubicError quadraticBound cubicBound coordinateFactor
  positivity
open _root_.P2M7374ab17 renaming h244 → _p2mH244
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h240 (security bits order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (conditionalQuadratic security bits order scalar.val) arity colors centers-
      data security order (LegBackgroundFamilies.conditionalQuadratic security order horder scalar) arity colors centers| ≤
      conditionalQuadraticError security order*(1/(2:ℝ)^bits) := by
  have hprod := _p2mH104 security bits order
    (ConditionalPairLinear.certificate security order (by omega) scalar) (translationCertificate security order (by omega) scalar.val)
    (RationalConditionalPairProgram.current security bits order scalar.val) (RationalBackgroundProgram.translation security bits order scalar.val)
    (conditionalLinearBound security order) (RationalBackgroundLinearProgram.translationBound security order)
    (RationalConditionalPairProgram.errorConstant security) (RationalBackgroundProgram.translationErrorConstant security)
    (by unfold conditionalLinearBound coordinateFactor; positivity) (by unfold RationalBackgroundLinearProgram.translationBound; positivity)
    (_p2mH160 security) (_p2mH248 security)
    (_p2mH239 security order (by omega) scalar) (_p2mH125 security order (by omega) scalar.val)
    (_p2mH158 security bits order (by omega) scalar hfirst hprecision hbudget)
    (_p2mH151 security bits order (by omega) scalar.val hfirst hprecision hbudget) arity colors centers
  have hpair := _p2mH291 security bits order horder scalar hfirst hprecision hbudget arity colors centers
  have hinterpret : interpret security order (conditionalQuadratic security bits order scalar.val) =
      interpret security order (RationalPairQuadraticProgram.current security bits order scalar.val)+
      interpret security order (RationalFamilyProductProgram.product order (RationalConditionalPairProgram.current security bits order scalar.val)
        (RationalBackgroundProgram.translation security bits order scalar.val)) := by
    funext arity colors centers
    exact Rat.cast_add _ _
  rw [hinterpret]
  change |((_:ℝ)+(_:ℝ))-((_:ℝ)+(_:ℝ))| ≤ (_:ℝ)
  rw [show ∀ a b c d : ℝ, a+b-(c+d)=(a-c)+(b-d) by intros; ring]
  exact (abs_add_le _ _).trans ((add_le_add hpair hprod).trans_eq (by unfold conditionalQuadraticError; ring))
open _root_.P2M7374ab17 renaming h240 → _p2mH240
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h238 (security bits order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (conditionalCubic security bits order scalar.val) arity colors centers-
      data security order (LegBackgroundFamilies.conditionalCubic security order horder scalar) arity colors centers| ≤
      conditionalCubicError security order*(1/(2:ℝ)^bits) :=
  _p2mH104 security bits order
    (PairQuadraticFamilies.pairQuadraticCertificate security order horder scalar) (translationCertificate security order (by omega) scalar.val)
    (RationalPairQuadraticProgram.current security bits order scalar.val) (RationalBackgroundProgram.translation security bits order scalar.val)
    (pairBound security order) (RationalBackgroundLinearProgram.translationBound security order)
    (RationalPairQuadraticProgram.errorConstant security order) (RationalBackgroundProgram.translationErrorConstant security)
    (by unfold pairBound coordinateFactor; positivity) (by unfold RationalBackgroundLinearProgram.translationBound; positivity)
    (_p2mH293 security order) (_p2mH248 security)
    (_p2mH245 security order horder scalar) (_p2mH125 security order (by omega) scalar.val)
    (_p2mH291 security bits order horder scalar hfirst hprecision hbudget)
    (_p2mH151 security bits order (by omega) scalar.val hfirst hprecision hbudget) arity colors centers
open _root_.P2M7374ab17 renaming h238 → _p2mH238
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h247 (security bits order : ℕ) (horder : 2 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (quadratic security bits order) arity colors centers-
      data security order (LegBackgroundFamilies.legQuadratic security order horder) arity colors centers| ≤
      (conditionalQuadraticError security order+quadraticBound security order)*(1/(2:ℝ)^bits) :=
  _p2mH323 security bits order
    (LegBackgroundFamilies.conditionalQuadratic security order horder) (conditionalQuadratic security bits order)
    (quadraticBound security order) (conditionalQuadraticError security order) (by unfold quadraticBound coordinateFactor; positivity)
    (_p2mH246 security order horder) (fun scalar => _p2mH240 security bits order horder scalar hfirst hprecision hbudget)
    arity colors centers
open _root_.P2M7374ab17 renaming h247 → _p2mH247
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h242 (security bits order : ℕ) (horder : 2 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (cubic security bits order) arity colors centers-
      data security order (LegBackgroundFamilies.legCubic security order horder) arity colors centers| ≤
      (conditionalCubicError security order+cubicBound security order)*(1/(2:ℝ)^bits) :=
  _p2mH323 security bits order
    (LegBackgroundFamilies.conditionalCubic security order horder) (conditionalCubic security bits order)
    (cubicBound security order) (conditionalCubicError security order) (by unfold cubicBound coordinateFactor; positivity)
    (_p2mH241 security order horder) (fun scalar => _p2mH238 security bits order horder scalar hfirst hprecision hbudget)
    arity colors centers
open _root_.P2M7374ab17 renaming h242 → _p2mH242
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h243 (security bits order : ℕ) (horder : 2 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (LegBackgroundFamilies.completeLegAtom security order horder arity).val colors centers| ≤
      errorConstant security order*(1/(2:ℝ)^bits) := by
  have hl := _p2mH120 security bits order (by omega) hfirst hprecision hbudget arity colors centers
  have hq := _p2mH247 security bits order horder hfirst hprecision hbudget arity colors centers
  have hc := _p2mH242 security bits order horder hfirst hprecision hbudget arity colors centers
  simp only [current, Rat.cast_add, LegBackgroundFamilies.completeLegAtom, Pi.add_apply, Submodule.coe_add]
  rw [show ∀ a b c A B C : ℝ, a+b+c-(A+B+C)=(a-A)+(b-B)+(c-C) by intros; ring]
  exact (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add hl hq)) hc).trans_eq
    (by unfold errorConstant; ring))
open _root_.P2M7374ab17 renaming h243 → _p2mH243
end
open _root_.P2M7374ab17 renaming h238 → _p2mH238
open _root_.P2M7374ab17 renaming h239 → _p2mH239
open _root_.P2M7374ab17 renaming h240 → _p2mH240
open _root_.P2M7374ab17 renaming h241 → _p2mH241
open _root_.P2M7374ab17 renaming h242 → _p2mH242
open _root_.P2M7374ab17 renaming h243 → _p2mH243
open _root_.P2M7374ab17 renaming h244 → _p2mH244
open _root_.P2M7374ab17 renaming h245 → _p2mH245
open _root_.P2M7374ab17 renaming h246 → _p2mH246
open _root_.P2M7374ab17 renaming h247 → _p2mH247
open _root_.P2M7374ab17 renaming h248 → _p2mH248
open _root_.P2M7374ab17 renaming h333 → _p2mH333
end CurrentAFT.RationalLegBackgroundProgram
open _root_.P2M7374ab17 renaming h238 → _p2mH238
open _root_.P2M7374ab17 renaming h239 → _p2mH239
open _root_.P2M7374ab17 renaming h240 → _p2mH240
open _root_.P2M7374ab17 renaming h241 → _p2mH241
open _root_.P2M7374ab17 renaming h242 → _p2mH242
open _root_.P2M7374ab17 renaming h243 → _p2mH243
open _root_.P2M7374ab17 renaming h244 → _p2mH244
open _root_.P2M7374ab17 renaming h245 → _p2mH245
open _root_.P2M7374ab17 renaming h246 → _p2mH246
open _root_.P2M7374ab17 renaming h247 → _p2mH247
open _root_.P2M7374ab17 renaming h248 → _p2mH248
open _root_.P2M7374ab17 renaming h333 → _p2mH333
end
open _root_.P2M7374ab17 renaming h241 → _p2mH241
open _root_.P2M7374ab17 renaming h248 → _p2mH248
open _root_.P2M7374ab17 renaming h242 → _p2mH242
open _root_.P2M7374ab17 renaming h244 → _p2mH244
open _root_.P2M7374ab17 renaming h239 → _p2mH239
open _root_.P2M7374ab17 renaming h240 → _p2mH240
open _root_.P2M7374ab17 renaming h245 → _p2mH245
open _root_.P2M7374ab17 renaming h247 → _p2mH247
open _root_.P2M7374ab17 renaming h243 → _p2mH243
open _root_.P2M7374ab17 renaming h238 → _p2mH238
open _root_.P2M7374ab17 renaming h246 → _p2mH246
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h221 {Primary Body : Type*} (order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Primary) (centers : Fin arity.val.2.val → Body) :
    |unit (Scalar := ℝ) order arity colors centers| ≤ 1 := by
  unfold unit
  split_ifs <;> norm_num
open _root_.P2M7374ab17 renaming h221 → _p2mH221
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h208 {Primary Body : Type*} (order : ℕ) (table : Table ℝ Primary Body order)
    (bound scale : ℝ) (hb : 0 ≤ bound) (hs : 1 ≤ scale)
    (hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * bound ≤ scale)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound) (count : ℕ)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |power order table count arity colors centers| ≤ scale^count := by
  induction count generalizing arity colors centers with
  | zero => simpa only [power, pow_zero] using _p2mH221 order arity colors centers
  | succ count ih =>
      have h := _p2mH213 order (power order table count) table (scale^count) bound
        (pow_nonneg (by linarith) _) hb ih htable arity colors centers
      simp only [Fintype.card_eq_nat_card] at h
      apply h.trans
      have hm := mul_le_mul_of_nonneg_left hscale (pow_nonneg (by linarith : 0 ≤ scale) count)
      rw [pow_succ scale count]
      convert hm using 1
      ring
open _root_.P2M7374ab17 renaming h208 → _p2mH208
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h200 (order : ℕ) (bound error : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) :
    1 ≤ growth order bound error := by
  unfold growth
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (by positivity))
open _root_.P2M7374ab17 renaming h200 → _p2mH200
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h201 (order : ℕ) (bound error : ℝ) :
    (Nat.card (TruncatedArity order) : ℝ)^2 * (bound + error + 1) ≤ growth order bound error := by
  unfold growth
  linarith
open _root_.P2M7374ab17 renaming h201 → _p2mH201
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h210 {Primary Body : Type*} (order : ℕ) (table computed : Table ℝ Primary Body order)
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
      have hp := _p2mH208 order table bound scale hb hs hbase htable count
      have h := _p2mH215 order (power order table count) (power order computed count) table computed
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
open _root_.P2M7374ab17 renaming h210 → _p2mH210
end
open _root_.P2M7374ab17 renaming h200 → _p2mH200
open _root_.P2M7374ab17 renaming h201 → _p2mH201
open _root_.P2M7374ab17 renaming h208 → _p2mH208
open _root_.P2M7374ab17 renaming h210 → _p2mH210
open _root_.P2M7374ab17 renaming h221 → _p2mH221
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M7374ab17 renaming h200 → _p2mH200
open _root_.P2M7374ab17 renaming h201 → _p2mH201
open _root_.P2M7374ab17 renaming h208 → _p2mH208
open _root_.P2M7374ab17 renaming h210 → _p2mH210
open _root_.P2M7374ab17 renaming h221 → _p2mH221
end
open _root_.P2M7374ab17 renaming h201 → _p2mH201
open _root_.P2M7374ab17 renaming h208 → _p2mH208
open _root_.P2M7374ab17 renaming h210 → _p2mH210
open _root_.P2M7374ab17 renaming h221 → _p2mH221
open _root_.P2M7374ab17 renaming h200 → _p2mH200
section
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h198 {Primary Body : Type*} (order population : ℕ)
    (table computed : Table ℝ Primary Body order) (bound error : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound)
    (herror : ∀ arity colors centers, |computed arity colors centers - table arity colors centers| ≤ error)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |binomial order population computed arity colors centers - binomial order population table arity colors centers| ≤
      ((population+1 : ℕ):ℝ)^(order+1) * ((order+1 : ℕ):ℝ)^2 * error *
        (growth order bound error)^(order+1) := by
  let scale := growth order bound error
  have hs : 1 ≤ scale := _p2mH200 order bound error hb he
  unfold binomial
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _count ∈ Finset.range (order+1),
        ((population+1 : ℕ):ℝ)^(order+1) * (((order+1 : ℕ):ℝ)*error*scale^(order+1)) := by
      apply Finset.sum_le_sum
      intro count hcount
      have hc : count ≤ order+1 := by have := Finset.mem_range.mp hcount; omega
      have hchoose : (population.choose count : ℝ) ≤ ((population+1 : ℕ):ℝ)^(order+1) := by
        exact_mod_cast (Nat.choose_le_pow population count).trans
          ((Nat.pow_le_pow_left (by omega : population ≤ population+1) count).trans
            (Nat.pow_le_pow_right (by omega : 1 ≤ population+1) hc))
      have hp := _p2mH210 order table computed bound error scale hb he hs
        (_p2mH201 order bound error) htable herror count arity colors centers
      have hp' : |power order computed count arity colors centers-power order table count arity colors centers| ≤
          ((order+1 : ℕ):ℝ)*error*scale^(order+1) := by
        apply hp.trans
        exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) he)
          (pow_le_pow_right₀ hs hc) (by positivity) (by positivity)
      rw [← mul_sub, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ population.choose count by positivity)]
      exact mul_le_mul hchoose hp' (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; dsimp only [scale]; ring
open _root_.P2M7374ab17 renaming h198 → _p2mH198
end
open _root_.P2M7374ab17 renaming h198 → _p2mH198
end CurrentAFT.RationalFamilyProductProgram
open _root_.P2M7374ab17 renaming h198 → _p2mH198
end
open _root_.P2M7374ab17 renaming h198 → _p2mH198
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
theorem _root_.P2M7374ab17.h300 (security order population : ℕ)
    (table : RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    interpret security order (RationalFamilyProductProgram.binomial order population table) =
      RationalFamilyProductProgram.binomial order population (interpret security order table) := by
  unfold interpret
  rw [_p2mH197, _p2mH216]
open _root_.P2M7374ab17 renaming h300 → _p2mH300
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h298 (security order population : ℕ) (family : ActualFamily security order)
    (hzero : family (zeroArity order)=0) :
    RationalFamilyProductProgram.binomial order population (data security order family) =
      data security order ((1+family)^population) :=
  _p2mH196 (ProposalPrimary.primaryLaw security) (bodyReference security)
    order population family hzero
open _root_.P2M7374ab17 renaming h298 → _p2mH298
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h297 (order population : ℕ) (A : ℝ) (hA : 0 ≤ A) : 0 ≤ bound order population A := by
  have hg := (_p2mH200 order A 0 hA (by norm_num)).trans' (by norm_num : (0:ℝ)≤1)
  unfold bound
  positivity
open _root_.P2M7374ab17 renaming h297 → _p2mH297
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h299 (order population : ℕ) (A e : ℝ) (hA : 0 ≤ A) (he : 0 ≤ e) :
    0 ≤ error order population A e := by
  have hg := (_p2mH200 order A e hA he).trans' (by norm_num : (0:ℝ)≤1)
  unfold error
  positivity
open _root_.P2M7374ab17 renaming h299 → _p2mH299
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h295 (security order population : ℕ) (family : ActualFamily security order)
    (hzero : family (zeroArity order)=0) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ arity colors centers, |data security order family arity colors centers| ≤ A)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |data security order ((1+family)^population) arity colors centers| ≤ bound order population A := by
  rw [← _p2mH298 security order population family hzero]
  let scale := RationalFamilyProductProgram.growth order A 0
  have hs : 1 ≤ scale := _p2mH200 order A 0 hA (by norm_num)
  have hscale : (Nat.card (TruncatedArity order):ℝ)^2*A ≤ scale := by
    unfold scale RationalFamilyProductProgram.growth
    nlinarith [sq_nonneg (Nat.card (TruncatedArity order):ℝ)]
  unfold RationalFamilyProductProgram.binomial
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _count ∈ Finset.range (order+1), ((population+1:ℕ):ℝ)^(order+1)*scale^(order+1) := by
      apply Finset.sum_le_sum
      intro count hcount
      have hc : count ≤ order+1 := by have := Finset.mem_range.mp hcount; omega
      have hn : (population.choose count:ℝ) ≤ ((population+1:ℕ):ℝ)^(order+1) := by
        exact_mod_cast (Nat.choose_le_pow population count).trans
          ((Nat.pow_le_pow_left (by omega : population≤population+1) count).trans (Nat.pow_le_pow_right (by omega : 1≤population+1) hc))
      have hp := (_p2mH208 order (data security order family) A scale hA hs hscale ha count arity colors centers).trans
        (pow_le_pow_right₀ hs hc)
      rw [abs_mul, abs_of_nonneg (show (0:ℝ)≤population.choose count by positivity)]
      exact mul_le_mul hn hp (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, bound]; dsimp only [scale]; ring
open _root_.P2M7374ab17 renaming h295 → _p2mH295
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h296 (security bits order population : ℕ) (family : ActualFamily security order)
    (hzero : family (zeroArity order)=0) (table : RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (A e : ℝ) (hA : 0 ≤ A) (he : 0 ≤ e)
    (ha : ∀ arity colors centers, |data security order family arity colors centers| ≤ A)
    (hea : ∀ arity colors centers, |interpret security order table arity colors centers-data security order family arity colors centers| ≤ e*(1/(2:ℝ)^bits))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (RationalFamilyProductProgram.binomial order population table) arity colors centers-
      data security order ((1+family)^population) arity colors centers| ≤ error order population A e*(1/(2:ℝ)^bits) := by
  have hε : (0:ℝ)≤1/2^bits := by positivity
  have hε1 : 1/(2:ℝ)^bits ≤ 1 :=
    (div_le_one (by positivity : (0:ℝ)<2^bits)).mpr (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  rw [_p2mH300, ← _p2mH298 security order population family hzero]
  have h := _p2mH198 order population (data security order family)
    (interpret security order table) A (e*(1/(2:ℝ)^bits)) hA (mul_nonneg he hε) ha hea arity colors centers
  apply h.trans
  have hg : RationalFamilyProductProgram.growth order A (e*(1/(2:ℝ)^bits)) ≤ RationalFamilyProductProgram.growth order A e := by
    unfold RationalFamilyProductProgram.growth
    nlinarith [mul_le_mul_of_nonneg_left hε1 he, sq_nonneg (Nat.card (TruncatedArity order):ℝ)]
  calc
    _ ≤ ((population+1:ℕ):ℝ)^(order+1)*((order+1:ℕ):ℝ)^2*(e*(1/(2:ℝ)^bits))*
        (RationalFamilyProductProgram.growth order A e)^(order+1) := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by have := _p2mH200 order A (e*(1/(2:ℝ)^bits)) hA (mul_nonneg he hε); linarith) hg _)
      positivity
    _ = _ := by unfold error; ring
open _root_.P2M7374ab17 renaming h296 → _p2mH296
end
open _root_.P2M7374ab17 renaming h295 → _p2mH295
open _root_.P2M7374ab17 renaming h296 → _p2mH296
open _root_.P2M7374ab17 renaming h297 → _p2mH297
open _root_.P2M7374ab17 renaming h298 → _p2mH298
open _root_.P2M7374ab17 renaming h299 → _p2mH299
open _root_.P2M7374ab17 renaming h300 → _p2mH300
end CurrentAFT.RationalPopulationApproximation
open _root_.P2M7374ab17 renaming h295 → _p2mH295
open _root_.P2M7374ab17 renaming h296 → _p2mH296
open _root_.P2M7374ab17 renaming h297 → _p2mH297
open _root_.P2M7374ab17 renaming h298 → _p2mH298
open _root_.P2M7374ab17 renaming h299 → _p2mH299
open _root_.P2M7374ab17 renaming h300 → _p2mH300
end
open _root_.P2M7374ab17 renaming h298 → _p2mH298
open _root_.P2M7374ab17 renaming h297 → _p2mH297
open _root_.P2M7374ab17 renaming h295 → _p2mH295
open _root_.P2M7374ab17 renaming h299 → _p2mH299
open _root_.P2M7374ab17 renaming h300 → _p2mH300
open _root_.P2M7374ab17 renaming h296 → _p2mH296
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
theorem _root_.P2M7374ab17.h128 (security : ℕ) : freeCount security=BackgroundPopulationBounds.freeCount security := by
  simp only [freeCount, PublicParameterProgram.modulus_value, BackgroundPopulationBounds.freeCount,
    Parameters.bodySize_eq, Parameters.legCount_eq, Parameters.base]
open _root_.P2M7374ab17 renaming h128 → _p2mH128
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h130 (security order : ℕ) (horder : 2≤order) :
    ∀ arity colors centers, |data security order (LegBackgroundFamilies.completeLegAtom security order horder) arity colors centers| ≤ legAtomBound security order := by
  have hb : (1:ℝ)≤Parameters.base security := by
    exact_mod_cast (show 1≤Parameters.base security by have := Parameters.base_ge_two security; omega)
  exact _p2mH102 security order _ 43377248 ((LegBackgroundFamilies.completeLegAtom_norm security order horder).trans
    (div_le_self (by norm_num) (one_le_pow₀ hb)))
open _root_.P2M7374ab17 renaming h130 → _p2mH130
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h126 (security order : ℕ) :
    0≤freeBound security order ∧ 0≤queueBound security order ∧ 0≤legBound security order ∧
    0≤freeError security order ∧ 0≤queueError security order ∧ 0≤legError security order := by
  have hfA : 0≤RationalMarkedPairProgram.freeBound security order := by
    unfold RationalMarkedPairProgram.freeBound coordinateFactor; positivity
  have hqA : 0≤RationalBackgroundLinearProgram.translationBound security order := by
    unfold RationalBackgroundLinearProgram.translationBound; positivity
  have hlA : 0≤legAtomBound security order := by unfold legAtomBound coordinateFactor; positivity
  rcases _p2mH147 security with ⟨hp, _, hb⟩
  have hfE : 0≤RationalBackgroundProgram.freeErrorConstant security := by
    unfold RationalBackgroundProgram.freeErrorConstant; positivity
  exact ⟨_p2mH297 _ _ _ hfA,
    _p2mH297 _ _ _ hqA,
    _p2mH297 _ _ _ hlA,
    _p2mH299 _ _ _ _ hfA hfE,
    _p2mH299 _ _ _ _ hqA (_p2mH248 security),
    _p2mH299 _ _ _ _ hlA (_p2mH244 security order)⟩
open _root_.P2M7374ab17 renaming h126 → _p2mH126
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h129 (security order : ℕ) (horder : 2≤order) :
    ∀ arity colors centers, |data security order (freeActual security order horder) arity colors centers| ≤ freeBound security order :=
  _p2mH295 security order _ _ (freeCertificate_zero security order (by omega))
    _ (by unfold RationalMarkedPairProgram.freeBound coordinateFactor; positivity) (_p2mH255 security order (by omega))
open _root_.P2M7374ab17 renaming h129 → _p2mH129
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h132 (security order : ℕ) (horder : 2≤order) (queue : ℤ) :
    ∀ arity colors centers, |data security order (queueActual security order horder queue) arity colors centers| ≤ queueBound security order :=
  _p2mH295 security order _ _ (translationCertificate_zero security order (by omega) queue)
    _ (by unfold RationalBackgroundLinearProgram.translationBound; positivity) (_p2mH125 security order (by omega) queue)
open _root_.P2M7374ab17 renaming h132 → _p2mH132
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h131 (security order : ℕ) (horder : 2≤order) :
    ∀ arity colors centers, |data security order (legActual security order horder) arity colors centers| ≤ legBound security order :=
  _p2mH295 security order _ _ (completeLegAtom_zero security order horder)
    _ (by unfold legAtomBound coordinateFactor; positivity) (_p2mH130 security order horder)
open _root_.P2M7374ab17 renaming h131 → _p2mH131
set_option maxRecDepth 8192
theorem _root_.P2M7374ab17.h127 (security bits order : ℕ) (horder : 2≤order) (queue : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    (∀ arity colors centers, |interpret security order (freeFactor security bits order) arity colors centers-
      data security order (freeActual security order horder) arity colors centers| ≤ freeError security order*(1/(2:ℝ)^bits)) ∧
    (∀ arity colors centers, |interpret security order (queueFactor security bits order queue) arity colors centers-
      data security order (queueActual security order horder queue) arity colors centers| ≤ queueError security order*(1/(2:ℝ)^bits)) ∧
    (∀ arity colors centers, |interpret security order (legFactor security bits order) arity colors centers-
      data security order (legActual security order horder) arity colors centers| ≤ legError security order*(1/(2:ℝ)^bits)) := by
  rcases _p2mH147 security with ⟨hp, _, hb⟩
  have hfE : 0≤RationalBackgroundProgram.freeErrorConstant security := by
    unfold RationalBackgroundProgram.freeErrorConstant; positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold freeFactor
    rw [_p2mH128]
    exact _p2mH296 security bits order _ _ (freeCertificate_zero security order (by omega)) _ _ _
      (by unfold RationalMarkedPairProgram.freeBound coordinateFactor; positivity) hfE
      (_p2mH255 security order (by omega))
      (_p2mH149 security bits order (by omega) hfirst hprecision hbudget)
  · unfold queueFactor
    rw [PublicParameterProgram.modulus_value]
    exact _p2mH296 security bits order _ _ (translationCertificate_zero security order (by omega) queue) _ _ _
      (by unfold RationalBackgroundLinearProgram.translationBound; positivity) (_p2mH248 security)
      (_p2mH125 security order (by omega) queue)
      (_p2mH151 security bits order (by omega) queue hfirst hprecision hbudget)
  · unfold legFactor
    have hl : (security+2)^128=Parameters.legCount security := by simp only [Parameters.legCount_eq, Parameters.base]
    rw [hl]
    have hA : 0≤legAtomBound security order := by
      exact mul_nonneg (pow_nonneg
        (mul_nonneg (mul_nonneg (show (0:ℝ)≤2 by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) order)
        (show (0:ℝ)≤43377248 by norm_num)
    have hE := _p2mH244 security order
    have hpoint : ∀ arity colors centers,
        |interpret security order (RationalLegBackgroundProgram.current security bits order) arity colors centers-
          data security order (LegBackgroundFamilies.completeLegAtom security order horder) arity colors centers| ≤
        RationalLegBackgroundProgram.errorConstant security order*(1/(2:ℝ)^bits) := by
      intro arity colors centers
      exact _p2mH243 security bits order horder hfirst hprecision hbudget arity colors centers
    intro arity colors centers
    have h := _p2mH296 security bits order (Parameters.legCount security)
      (LegBackgroundFamilies.completeLegAtom security order horder) (completeLegAtom_zero security order horder)
      (RationalLegBackgroundProgram.current security bits order) (legAtomBound security order)
      (RationalLegBackgroundProgram.errorConstant security order) hA hE (_p2mH130 security order horder)
      hpoint arity colors centers
    exact h
open _root_.P2M7374ab17 renaming h127 → _p2mH127
set_option maxRecDepth 8192
theorem _root_.CurrentAFT.RationalBackgroundPopulationProgram.__p2m_proof_7374ab17fd2d57b3080a (security bits order : ℕ) (horder : 2≤order) (queue : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order queue arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (ActualBackground.fixedQueueBackground security order horder queue arity).val colors centers| ≤
      errorConstant security order*(1/(2:ℝ)^bits) := by
  rcases _p2mH126 security order with ⟨hf, hq, hl, heF, heQ, heL⟩
  rcases _p2mH127 security bits order horder queue hfirst hprecision hbudget with ⟨hfree, hqueue, hleg⟩
  have hfirstError := _p2mH104 security bits order (freeActual security order horder) (queueActual security order horder queue)
    (freeFactor security bits order) (queueFactor security bits order queue)
    (freeBound security order) (queueBound security order) (freeError security order) (queueError security order)
    hf hq heF heQ (_p2mH129 security order horder) (_p2mH132 security order horder queue) hfree hqueue
  have hfirstBound : ∀ arity colors centers,
      |data security order (freeActual security order horder*queueActual security order horder queue) arity colors centers| ≤ freeQueueBound security order := by
    intro arity colors centers
    change |data security order (familyProduct (ProposalPrimary.primaryLaw security) (bodyReference security) order
      (freeActual security order horder) (queueActual security order horder queue)) arity colors centers| ≤ _
    rw [← _p2mH100]
    exact (_p2mH213 order _ _ _ _ hf hq
      (_p2mH129 security order horder) (_p2mH132 security order horder queue) arity colors centers).trans_eq
        (by unfold freeQueueBound; ring)
  have hbFQ : 0≤freeQueueBound security order := by unfold freeQueueBound; positivity
  have heFQ : 0≤freeQueueError security order := _p2mH103 _ _ _ _ _ hf hq heF heQ
  exact _p2mH104 security bits order (freeActual security order horder*queueActual security order horder queue)
    (legActual security order horder)
    (RationalFamilyProductProgram.product order (freeFactor security bits order) (queueFactor security bits order queue))
    (legFactor security bits order) (freeQueueBound security order) (legBound security order)
    (freeQueueError security order) (legError security order) hbFQ hl heFQ heL hfirstBound
    (_p2mH131 security order horder) hfirstError hleg arity colors centers
end
open _root_.P2M7374ab17 renaming h126 → _p2mH126
open _root_.P2M7374ab17 renaming h127 → _p2mH127
open _root_.P2M7374ab17 renaming h128 → _p2mH128
open _root_.P2M7374ab17 renaming h129 → _p2mH129
open _root_.P2M7374ab17 renaming h130 → _p2mH130
open _root_.P2M7374ab17 renaming h131 → _p2mH131
open _root_.P2M7374ab17 renaming h132 → _p2mH132
end CurrentAFT.RationalBackgroundPopulationProgram
open _root_.P2M7374ab17 renaming h126 → _p2mH126
open _root_.P2M7374ab17 renaming h127 → _p2mH127
open _root_.P2M7374ab17 renaming h128 → _p2mH128
open _root_.P2M7374ab17 renaming h129 → _p2mH129
open _root_.P2M7374ab17 renaming h130 → _p2mH130
open _root_.P2M7374ab17 renaming h131 → _p2mH131
open _root_.P2M7374ab17 renaming h132 → _p2mH132
end
open _root_.P2M7374ab17 renaming h131 → _p2mH131
open _root_.P2M7374ab17 renaming h132 → _p2mH132
open _root_.P2M7374ab17 renaming h128 → _p2mH128
open _root_.P2M7374ab17 renaming h127 → _p2mH127
open _root_.P2M7374ab17 renaming h130 → _p2mH130
open _root_.P2M7374ab17 renaming h126 → _p2mH126
open _root_.P2M7374ab17 renaming h129 → _p2mH129
set_option maxRecDepth 65536
theorem solution : (type_of% @_root_.CurrentAFT.RationalBackgroundPopulationProgram.__p2m_proof_7374ab17fd2d57b3080a) := @_root_.CurrentAFT.RationalBackgroundPopulationProgram.__p2m_proof_7374ab17fd2d57b3080a
