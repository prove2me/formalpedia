-- Prove2me | solution 1 for DerivativeChainPrivate.row10_complete_inverse_branches
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T22:35:03.520817+00:00
-- url     : https://prove2.me/submissions/90a852a2-3501-48f4-b4cc-696a897b0248

import Definitions.Def_DerivativeChainPrivate_fifth_row10_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row10_separation
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row10_branch_exists_1
import Theorems.Thm_DerivativeChainPrivate_row10_branch_exists_2
import Theorems.Thm_DerivativeChainPrivate_row10_branch_exists_3
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


section
-- Source module: HermiteVerified

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Polynomial
namespace DerivativeChainPrivate.Hermite















end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite









end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite























end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite

lemma root_between (p : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ x ∈ Set.Ioo a b, p.eval x = 0 := by
  obtain ⟨x,hx,hroot⟩ := intermediate_value_Icc hab.le p.continuous.continuousOn
    (show (0:ℝ) ∈ Set.Icc (p.eval a) (p.eval b) from ⟨ha.le,hb.le⟩)
  refine ⟨x,⟨?_,?_⟩,hroot⟩
  · by_contra hn
    have he : x = a := by linarith [hx.1]
    subst x; linarith
  · by_contra hn
    have he : x = b := by linarith [hx.2]
    subst x; linarith









end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite













end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite





end DerivativeChainPrivate.Hermite

end


section
-- Source module: SepticSqrtAlgebra


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators















theorem norm_real_power_sum_le {n : ℕ} (c : Fin n → ℝ) (u : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hu : ‖u‖ ≤ R) :
    ‖∑ i : Fin n, (c i:ℂ)*u^i.val‖ ≤ ∑ i : Fin n, |c i| *R^i.val := by
  calc
    _ ≤ ∑ i : Fin n, ‖(c i:ℂ)*u^i.val‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      gcongr











end DerivativeChainPrivate

end


section
-- Source module: CubicRootCover

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cubic_three_roots_cover (g0 g1 g2 g3 a b c v : ℂ)
    (hg3 : g3 ≠ 0) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : g0+g1*a+g2*a^2+g3*a^3=0)
    (hb : g0+g1*b+g2*b^2+g3*b^3=0)
    (hc : g0+g1*c+g2*c^2+g3*c^3=0)
    (hv : g0+g1*v+g2*v^2+g3*v^3=0) : v=a ∨ v=b ∨ v=c := by
  have hB : g1+g2*(b+a)+g3*(b^2+b*a+a^2)=0 := by
    have hh : (b-a)*(g1+g2*(b+a)+g3*(b^2+b*a+a^2))=0 := by linear_combination hb-ha
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hab.symm)
  have hC : g1+g2*(c+a)+g3*(c^2+c*a+a^2)=0 := by
    have hh : (c-a)*(g1+g2*(c+a)+g3*(c^2+c*a+a^2))=0 := by linear_combination hc-ha
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hac.symm)
  have hsum : g2+g3*(a+b+c)=0 := by
    have hh : (b-c)*(g2+g3*(a+b+c))=0 := by linear_combination hB-hC
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hbc)
  have hf : g0+g1*v+g2*v^2+g3*v^3=g3*(v-a)*(v-b)*(v-c) := by
    linear_combination ha+(v-a)*hB+(v-a)*(v-b)*hsum
  rw [hf] at hv
  rcases mul_eq_zero.mp hv with h|h
  · rcases mul_eq_zero.mp h with h|h
    · have hh := (mul_eq_zero.mp h).resolve_left hg3
      exact Or.inl (sub_eq_zero.mp hh)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))
end DerivativeChainPrivate

end


section
-- Source module: NewtonSeparation

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem newton_branches_distinct (P₁ P₂ Y₁ Y₂ t : ℂ) (a b : ℝ)
    (ht : ‖t‖ ≤ 2) (hy₁ : ‖Y₁‖ ≤ 1/100000000000000) (hy₂ : ‖Y₂‖ ≤ 1/100000000000000)
    (hab : 1 < b-a) (happrox : ‖P₂-P₁-((b-a:ℝ):ℂ)‖ ≤ (9/10)*(b-a)) :
    P₁+t^32*Y₁ ≠ P₂+t^32*Y₂ := by
  have htail (Y : ℂ) (hy : ‖Y‖ ≤ 1/100000000000000) : ‖t^32*Y‖ ≤ 1/1000 := by
    rw [norm_mul,norm_pow]
    calc
      _ ≤ (2:ℝ)^32*(1/100000000000000) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ht 32) hy (norm_nonneg _) (by positivity)
      _ ≤ _ := by norm_num
  have h1 := htail Y₁ hy₁
  have h2 := htail Y₂ hy₂
  intro he
  have hid : ((b-a:ℝ):ℂ) = t^32*Y₁-t^32*Y₂-(P₂-P₁-((b-a:ℝ):ℂ)) := by linear_combination -he
  have hn : b-a ≤ ‖t^32*Y₁‖+‖t^32*Y₂‖+‖P₂-P₁-((b-a:ℝ):ℂ)‖ := by
    calc
      _ = ‖((b-a:ℝ):ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith only [hab])]
      _ = ‖t^32*Y₁-t^32*Y₂-(P₂-P₁-((b-a:ℝ):ℂ))‖ := congrArg norm hid
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  linarith only [hn,happrox,h1,h2,hab]
end DerivativeChainPrivate

end


section
-- Source module: QuadraticIntervalBound

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem quadratic_midpoint_bound (α m ε a b c : ℝ) (hα : |α-m| ≤ ε) :
    |a+b*α+c*α^2| ≤ |a+b*m+c*m^2|+ε*(|b+2*c*m|+|c| *ε) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hα
  have he : a+b*α+c*α^2 = (a+b*m+c*m^2)+(α-m)*(b+2*c*m)+c*(α-m)^2 := by ring
  rw [he]
  calc
    _ ≤ |a+b*m+c*m^2|+|(α-m)*(b+2*c*m)|+|c*(α-m)^2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |a+b*m+c*m^2|+ε*|b+2*c*m|+|c| *ε^2 := by
      simp only [abs_mul,abs_pow]
      gcongr
    _ = _ := by ring
end DerivativeChainPrivate

end


section
-- Source module: Row10AlphaRoots

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DerivativeChainPrivate
open Polynomial
theorem row10_alpha_exists_1 :
    ∃ α : ℝ, (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α ∧ α ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ∧ α^3=(1001/20)+(-66)*α+(21)*α^2 := by
  let p : Polynomial ℝ := (X^3-C (21)*X^2-C (-66)*X-C (1001/20))
  obtain ⟨α,hα,hroot⟩ := Hermite.root_between p (show (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) < (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) by norm_num)
    (by norm_num [p]) (by norm_num [p])
  refine ⟨α,hα.1.le,hα.2.le,?_⟩
  norm_num [p] at hroot
  linarith only [hroot]
theorem row10_alpha_exists_2 :
    ∃ α : ℝ, (97160973648365359300573924314704264662030400264262134485861186056383350158245991701430729829643120229512794018619323/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α ∧ α ≤ (24290243412091339825143481078676066165507600066065533621465296514095837539561497925357682457410780057378198504654831/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ∧ α^3=(1001/20)+(-66)*α+(21)*α^2 := by
  let p : Polynomial ℝ := -(X^3-C (21)*X^2-C (-66)*X-C (1001/20))
  obtain ⟨α,hα,hroot⟩ := Hermite.root_between p (show (97160973648365359300573924314704264662030400264262134485861186056383350158245991701430729829643120229512794018619323/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) < (24290243412091339825143481078676066165507600066065533621465296514095837539561497925357682457410780057378198504654831/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) by norm_num)
    (by norm_num [p]) (by norm_num [p])
  refine ⟨α,hα.1.le,hα.2.le,?_⟩
  norm_num [p] at hroot
  linarith only [hroot]
theorem row10_alpha_exists_3 :
    ∃ α : ℝ, (342113602974777971780177930530474855198990249462270615508012205216651868652496554890450202993505122452981721333792045/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α ∧ α ≤ (684227205949555943560355861060949710397980498924541231016024410433303737304993109780900405987010244905963442667584091/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ∧ α^3=(1001/20)+(-66)*α+(21)*α^2 := by
  let p : Polynomial ℝ := (X^3-C (21)*X^2-C (-66)*X-C (1001/20))
  obtain ⟨α,hα,hroot⟩ := Hermite.root_between p (show (342113602974777971780177930530474855198990249462270615508012205216651868652496554890450202993505122452981721333792045/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) < (684227205949555943560355861060949710397980498924541231016024410433303737304993109780900405987010244905963442667584091/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) by norm_num)
    (by norm_num [p]) (by norm_num [p])
  refine ⟨α,hα.1.le,hα.2.le,?_⟩
  norm_num [p] at hroot
  linarith only [hroot]
end DerivativeChainPrivate

end


section
-- Source module: Row10Difference

set_option autoImplicit false
set_option maxHeartbeats 0
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_polynomial_difference (a b : ℝ) (t : ℂ) :
    row10P b t-row10P a t-((b-a:ℝ):ℂ) =
      ((b-a:ℝ):ℂ)*t*(∑ i : Fin 31, (row10DifferenceCoeffs (a+b) i:ℂ)*t^i.val) := by
  norm_num [row10P,row10PCoeffs,row10DifferenceCoeffs,Fin.sum_univ_succ]
  push_cast
  ring
end DerivativeChainPrivate

end


section
-- Source module: Row10Separation12

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_difference_bound_12 (a b : ℝ)
    (hal : (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ a) (hau : a ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ))
    (hbl : (97160973648365359300573924314704264662030400264262134485861186056383350158245991701430729829643120229512794018619323/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ b) (hbu : b ≤ (24290243412091339825143481078676066165507600066065533621465296514095837539561497925357682457410780057378198504654831/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) (t : ℂ) (ht : ‖t‖ ≤ 5/4) :
    1 < b-a ∧ ‖row10P b t-row10P a t-((b-a:ℝ):ℂ)‖ ≤ (9/10)*(b-a) := by
  have hgap : 1 < b-a := by linarith only [hau,hbl]
  refine ⟨hgap,?_⟩
  have hm : |a+b-(71607462087364059948751990521033089754347012877616574505444875527928209948224156529399592682786491775487872564429523/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408)| ≤ (1/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) := by rw [abs_le]; constructor <;> linarith only [hal,hau,hbl,hbu]
  have hcoeff : ∀ k : Fin 31, |row10DifferenceCoeffs (a+b) k| ≤ row10DifferenceBounds12 k := by
    intro k
    fin_cases k
    all_goals
      dsimp [row10DifferenceCoeffs,row10DifferenceBounds12]
      apply (quadratic_midpoint_bound (a+b) (71607462087364059948751990521033089754347012877616574505444875527928209948224156529399592682786491775487872564429523/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408) (1/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816) _ _ _ hm).trans
      norm_num
  rw [row10_polynomial_difference,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith only [hgap])]
  have hnorm := norm_real_power_sum_le (row10DifferenceCoeffs (a+b)) t (5/4) (by norm_num) ht
  have hsum : (∑ k : Fin 31, |row10DifferenceCoeffs (a+b) k| *(5/4:ℝ)^k.val) ≤
      ∑ k : Fin 31, row10DifferenceBounds12 k*(5/4:ℝ)^k.val := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (hcoeff k) (by positivity)
  have hs : (5/4:ℝ)*(∑ k : Fin 31, row10DifferenceBounds12 k*(5/4:ℝ)^k.val) ≤ 9/10 := by
    norm_num [row10DifferenceBounds12,Fin.sum_univ_succ]
  calc
    _ ≤ (b-a)*(5/4)*(∑ k : Fin 31, row10DifferenceBounds12 k*(5/4:ℝ)^k.val) := by gcongr; exact hnorm.trans hsum
    _ ≤ (9/10)*(b-a) := by nlinarith only [mul_le_mul_of_nonneg_left hs (by linarith only [hgap] : 0 ≤ b-a)]
end DerivativeChainPrivate

end


section
-- Source module: Row10Separation13

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_difference_bound_13 (a b : ℝ)
    (hal : (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ a) (hau : a ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ))
    (hbl : (342113602974777971780177930530474855198990249462270615508012205216651868652496554890450202993505122452981721333792045/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ b) (hbu : b ≤ (684227205949555943560355861060949710397980498924541231016024410433303737304993109780900405987010244905963442667584091/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) (t : ℂ) (ht : ‖t‖ ≤ 5/4) :
    1 < b-a ∧ ‖row10P b t-row10P a t-((b-a:ℝ):ℂ)‖ ≤ (9/10)*(b-a) := by
  have hgap : 1 < b-a := by linarith only [hau,hbl]
  refine ⟨hgap,?_⟩
  have hm : |a+b-(730281156475918704157285917788311625244644124415512245541052975432776807043195431138268861522940108227426393777823813/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816)| ≤ (1/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) := by rw [abs_le]; constructor <;> linarith only [hal,hau,hbl,hbu]
  have hcoeff : ∀ k : Fin 31, |row10DifferenceCoeffs (a+b) k| ≤ row10DifferenceBounds13 k := by
    intro k
    fin_cases k
    all_goals
      dsimp [row10DifferenceCoeffs,row10DifferenceBounds13]
      apply (quadratic_midpoint_bound (a+b) (730281156475918704157285917788311625244644124415512245541052975432776807043195431138268861522940108227426393777823813/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816) (1/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816) _ _ _ hm).trans
      norm_num
  rw [row10_polynomial_difference,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith only [hgap])]
  have hnorm := norm_real_power_sum_le (row10DifferenceCoeffs (a+b)) t (5/4) (by norm_num) ht
  have hsum : (∑ k : Fin 31, |row10DifferenceCoeffs (a+b) k| *(5/4:ℝ)^k.val) ≤
      ∑ k : Fin 31, row10DifferenceBounds13 k*(5/4:ℝ)^k.val := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (hcoeff k) (by positivity)
  have hs : (5/4:ℝ)*(∑ k : Fin 31, row10DifferenceBounds13 k*(5/4:ℝ)^k.val) ≤ 9/10 := by
    norm_num [row10DifferenceBounds13,Fin.sum_univ_succ]
  calc
    _ ≤ (b-a)*(5/4)*(∑ k : Fin 31, row10DifferenceBounds13 k*(5/4:ℝ)^k.val) := by gcongr; exact hnorm.trans hsum
    _ ≤ (9/10)*(b-a) := by nlinarith only [mul_le_mul_of_nonneg_left hs (by linarith only [hgap] : 0 ≤ b-a)]
end DerivativeChainPrivate

end


section
-- Source module: Row10Separation23

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_difference_bound_23 (a b : ℝ)
    (hal : (97160973648365359300573924314704264662030400264262134485861186056383350158245991701430729829643120229512794018619323/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ a) (hau : a ≤ (24290243412091339825143481078676066165507600066065533621465296514095837539561497925357682457410780057378198504654831/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ))
    (hbl : (342113602974777971780177930530474855198990249462270615508012205216651868652496554890450202993505122452981721333792045/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ b) (hbu : b ≤ (684227205949555943560355861060949710397980498924541231016024410433303737304993109780900405987010244905963442667584091/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) (t : ℂ) (ht : ‖t‖ ≤ 5/4) :
    1 < b-a ∧ ‖row10P b t-row10P a t-((b-a:ℝ):ℂ)‖ ≤ (9/10)*(b-a) := by
  have hgap : 1 < b-a := by linarith only [hau,hbl]
  refine ⟨hgap,?_⟩
  have hm : |a+b-(390694089798960651430464892687826987530005449594401682750942798244843543731619550741165567908326682567738118343101707/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408)| ≤ (1/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) := by rw [abs_le]; constructor <;> linarith only [hal,hau,hbl,hbu]
  have hcoeff : ∀ k : Fin 31, |row10DifferenceCoeffs (a+b) k| ≤ row10DifferenceBounds23 k := by
    intro k
    fin_cases k
    all_goals
      dsimp [row10DifferenceCoeffs,row10DifferenceBounds23]
      apply (quadratic_midpoint_bound (a+b) (390694089798960651430464892687826987530005449594401682750942798244843543731619550741165567908326682567738118343101707/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408) (1/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816) _ _ _ hm).trans
      norm_num
  rw [row10_polynomial_difference,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith only [hgap])]
  have hnorm := norm_real_power_sum_le (row10DifferenceCoeffs (a+b)) t (5/4) (by norm_num) ht
  have hsum : (∑ k : Fin 31, |row10DifferenceCoeffs (a+b) k| *(5/4:ℝ)^k.val) ≤
      ∑ k : Fin 31, row10DifferenceBounds23 k*(5/4:ℝ)^k.val := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (hcoeff k) (by positivity)
  have hs : (5/4:ℝ)*(∑ k : Fin 31, row10DifferenceBounds23 k*(5/4:ℝ)^k.val) ≤ 9/10 := by
    norm_num [row10DifferenceBounds23,Fin.sum_univ_succ]
  calc
    _ ≤ (b-a)*(5/4)*(∑ k : Fin 31, row10DifferenceBounds23 k*(5/4:ℝ)^k.val) := by gcongr; exact hnorm.trans hsum
    _ ≤ (9/10)*(b-a) := by nlinarith only [mul_le_mul_of_nonneg_left hs (by linarith only [hgap] : 0 ≤ b-a)]
end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution :
    ∃ a1 a2 a3 : ℝ, ∃ Y1 Y2 Y3 : ℂ → ℂ,
      ((23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ a1 ∧ a1 ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) ∧ ((97160973648365359300573924314704264662030400264262134485861186056383350158245991701430729829643120229512794018619323/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ a2 ∧ a2 ≤ (24290243412091339825143481078676066165507600066065533621465296514095837539561497925357682457410780057378198504654831/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) ∧ ((342113602974777971780177930530474855198990249462270615508012205216651868652496554890450202993505122452981721333792045/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ a3 ∧ a3 ≤ (684227205949555943560355861060949710397980498924541231016024410433303737304993109780900405987010244905963442667584091/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) ∧
      (DifferentiableOn ℂ Y1 (Metric.ball 0 2) ∧
        (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y1 t‖ ≤ 1/100000000000000) ∧
        (∀ x : ℝ, |x| ≤ 2 → (Y1 (x:ℂ)).im=0)) ∧ (DifferentiableOn ℂ Y2 (Metric.ball 0 2) ∧
        (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y2 t‖ ≤ 1/100000000000000) ∧
        (∀ x : ℝ, |x| ≤ 2 → (Y2 (x:ℂ)).im=0)) ∧ (DifferentiableOn ℂ Y3 (Metric.ball 0 2) ∧
        (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y3 t‖ ≤ 1/100000000000000) ∧
        (∀ x : ℝ, |x| ≤ 2 → (Y3 (x:ℂ)).im=0)) ∧
      ∀ t : ℂ, ‖t‖ ≤ 5/4 → ∀ v : ℂ,
        row10G0 t+row10G1 t*v+row10G2 t*v^2+(-60)*v^3=0 →
        v=(row10P a1 t+t^32*Y1 t) ∨ v=(row10P a2 t+t^32*Y2 t) ∨ v=(row10P a3 t+t^32*Y3 t) := by
  obtain ⟨a1,hal1,hau1,ha1⟩ := row10_alpha_exists_1
  obtain ⟨Y1,hol1,hstate1,hreal1⟩ := row10_branch_exists_1 a1 hal1 hau1 ha1
  obtain ⟨a2,hal2,hau2,ha2⟩ := row10_alpha_exists_2
  obtain ⟨Y2,hol2,hstate2,hreal2⟩ := row10_branch_exists_2 a2 hal2 hau2 ha2
  obtain ⟨a3,hal3,hau3,ha3⟩ := row10_alpha_exists_3
  obtain ⟨Y3,hol3,hstate3,hreal3⟩ := row10_branch_exists_3 a3 hal3 hau3 ha3
  refine ⟨a1,a2,a3,Y1,Y2,Y3,⟨hal1,hau1⟩,⟨hal2,hau2⟩,⟨hal3,hau3⟩,
⟨hol1,fun t ht => (hstate1 t ht).1,hreal1⟩,⟨hol2,fun t ht => (hstate2 t ht).1,hreal2⟩,⟨hol3,fun t ht => (hstate3 t ht).1,hreal3⟩,?_⟩
  intro t ht v hv
  have ht2 : ‖t‖ ≤ 2 := by linarith only [ht]
  obtain ⟨hgap12,happrox12⟩ := row10_difference_bound_12 a1 a2 hal1 hau1 hal2 hau2 t ht
  have hne12 : (row10P a1 t+t^32*Y1 t) ≠ (row10P a2 t+t^32*Y2 t) :=
    newton_branches_distinct _ _ _ _ t a1 a2 ht2 (hstate1 t ht2).1 (hstate2 t ht2).1 hgap12 happrox12
  obtain ⟨hgap13,happrox13⟩ := row10_difference_bound_13 a1 a3 hal1 hau1 hal3 hau3 t ht
  have hne13 : (row10P a1 t+t^32*Y1 t) ≠ (row10P a3 t+t^32*Y3 t) :=
    newton_branches_distinct _ _ _ _ t a1 a3 ht2 (hstate1 t ht2).1 (hstate3 t ht2).1 hgap13 happrox13
  obtain ⟨hgap23,happrox23⟩ := row10_difference_bound_23 a2 a3 hal2 hau2 hal3 hau3 t ht
  have hne23 : (row10P a2 t+t^32*Y2 t) ≠ (row10P a3 t+t^32*Y3 t) :=
    newton_branches_distinct _ _ _ _ t a2 a3 ht2 (hstate2 t ht2).1 (hstate3 t ht2).1 hgap23 happrox23
  exact cubic_three_roots_cover (row10G0 t) (row10G1 t) (row10G2 t) (-60)
    (row10P a1 t+t^32*Y1 t) (row10P a2 t+t^32*Y2 t) (row10P a3 t+t^32*Y3 t) v (by norm_num) hne12 hne13 hne23
    (hstate1 t ht2).2 (hstate2 t ht2).2 (hstate3 t ht2).2 hv
