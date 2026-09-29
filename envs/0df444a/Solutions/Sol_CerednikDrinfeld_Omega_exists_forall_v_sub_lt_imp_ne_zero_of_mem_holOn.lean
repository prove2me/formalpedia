-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/508e9a78-7b44-58b8-9e26-775e73dbf14b

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn

set_option autoImplicit false

p2m_open "Filter Polynomial CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.holOn"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "RatPair RatPair.evalAt vRestrict v_lt_iff_vRestrict_lt tendstoUniformly_iff_vRestrict IsHolOn holOn"
namespace HolLocNV
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v : Valuation K Γ₀)

theorem pow_succ_le_self_of_le_one {a : Γ₀} (ha : a ≤ 1) (n : ℕ) : a ^ (n + 1) ≤ a := by
  rw [pow_succ]
  calc a ^ n * a ≤ 1 * a := mul_le_mul_left (pow_le_one' ha n) a
    _ = a := one_mul a

theorem exists_radius_poly (P : K[X]) (z₀ : K) {e : K} (he : e ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ z : K, v (z - z₀) < v c → v (P.eval z - P.eval z₀) < v e := by
  classical
  set Q : K[X] := taylor z₀ P with hQ

  let s : Finset K := insert 1 ((Finset.range Q.natDegree).image fun i => e / Q.coeff (i + 1))
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩

  let s' : Finset K := s.filter (fun x => x ≠ 0)
  have hs' : s'.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, one_ne_zero⟩⟩
  obtain ⟨c, hc, hcmin⟩ := s'.exists_min_image (fun x => v x) hs'
  have hc0 : c ≠ 0 := (Finset.mem_filter.mp hc).2
  have hc1 : v c ≤ 1 := by
    have := hcmin 1 (Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, one_ne_zero⟩)
    rwa [Valuation.map_one] at this
  refine ⟨c, hc0, fun z hz => ?_⟩
  set u := z - z₀ with hu
  have hu1 : v u ≤ 1 := (hz.trans_le hc1).le

  have hPz : P.eval z = Q.eval u := by
    rw [hQ, taylor_eval, hu, sub_add_cancel]
  have hPz₀ : P.eval z₀ = Q.coeff 0 := by rw [hQ, taylor_coeff_zero]
  have hdiff : P.eval z - P.eval z₀ = ∑ i ∈ Finset.range Q.natDegree, Q.coeff (i + 1) * u ^ (i + 1) := by
    rw [hPz, hPz₀, eval_eq_sum_range, Finset.sum_range_succ', pow_zero, mul_one, add_sub_cancel_right]
  rw [hdiff]
  have hepos : (0 : Γ₀) < v e := by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr he
  apply Valuation.map_sum_lt _ (ne_of_gt hepos)
  intro i hi
  by_cases ht : Q.coeff (i + 1) = 0
  · rw [ht, zero_mul, Valuation.map_zero]; exact hepos
  · have ht0 : v (Q.coeff (i + 1)) ≠ 0 := (Valuation.ne_zero_iff _).mpr ht
    have hmem : e / Q.coeff (i + 1) ∈ s' := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩), ?_⟩
      exact div_ne_zero he ht
    have hcle : v c ≤ v (e / Q.coeff (i + 1)) := hcmin _ hmem
    calc v (Q.coeff (i + 1) * u ^ (i + 1)) = v (Q.coeff (i + 1)) * v u ^ (i + 1) := by
          rw [Valuation.map_mul, Valuation.map_pow]
      _ ≤ v (Q.coeff (i + 1)) * v u := mul_le_mul_right (pow_succ_le_self_of_le_one hu1 i) _
      _ < v (Q.coeff (i + 1)) * v c := mul_lt_mul_of_pos_left hz (zero_lt_iff.mpr ht0)
      _ ≤ v (Q.coeff (i + 1)) * v (e / Q.coeff (i + 1)) := mul_le_mul_right hcle _
      _ = v e := by rw [← Valuation.map_mul, mul_div_cancel₀ _ ht]

theorem exists_radius_ratPair (r : RatPair K) {z₀ : K} (hq : r.den.eval z₀ ≠ 0) (hr : r.evalAt z₀ ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ z : K, v (z - z₀) < v c → v (r.evalAt z) = v (r.evalAt z₀) := by
  have hp : r.num.eval z₀ ≠ 0 := by
    intro h; apply hr; rw [RatPair.evalAt, h, zero_div]
  obtain ⟨cp, hcp, Hp⟩ := exists_radius_poly r.num z₀ hp
  obtain ⟨cq, hcq, Hq⟩ := exists_radius_poly r.den z₀ hq

  obtain ⟨c, hc0, hcp', hcq'⟩ : ∃ c : K, c ≠ 0 ∧ v c ≤ v cp ∧ v c ≤ v cq := by
    rcases le_total (v cp) (v cq) with h | h
    · exact ⟨cp, hcp, le_rfl, h⟩
    · exact ⟨cq, hcq, h, le_rfl⟩
  refine ⟨c, hc0, fun z hz => ?_⟩
  have h1 : v (r.num.eval z - r.num.eval z₀) < v (r.num.eval z₀) := Hp z (hz.trans_le hcp')
  have h2 : v (r.den.eval z - r.den.eval z₀) < v (r.den.eval z₀) := Hq z (hz.trans_le hcq')
  have hnum : v (r.num.eval z) = v (r.num.eval z₀) := Valuation.map_eq_of_sub_lt _ h1
  have hden : v (r.den.eval z) = v (r.den.eval z₀) := Valuation.map_eq_of_sub_lt _ h2
  rw [RatPair.evalAt, RatPair.evalAt, Valuation.map_div, Valuation.map_div, hnum, hden]

theorem exists_radius_of_isHolOn {S : Set K} {f : ↥S → K} (hf : IsHolOn K S f) (z₀ : ↥S) (hz₀ : f z₀ ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ z : ↥S, v ((z : K) - (z₀ : K)) < v c → f z ≠ 0 := by
  obtain ⟨r, hr, -, hlim⟩ := hf

  have hγ : vRestrict K (f z₀) ≠ 0 := (Valuation.ne_zero_iff _).mpr hz₀
  rw [tendstoUniformly_iff_vRestrict] at hlim
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (hlim (Units.mk0 _ hγ))
  have happrox : ∀ z : ↥S, v ((r k).evalAt z - f z) < v (f z₀) := fun z => by
    rw [v_lt_iff_vRestrict_lt]; exact hk k le_rfl z

  have h0 : v ((r k).evalAt z₀) = v (f z₀) := Valuation.map_eq_of_sub_lt _ (happrox z₀)
  have hv0 : v (f z₀) ≠ 0 := (Valuation.ne_zero_iff _).mpr hz₀
  have hr0 : (r k).evalAt z₀ ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at h0; exact hv0 h0.symm
  obtain ⟨c, hc, H⟩ := exists_radius_ratPair (r k) (hr k z₀ z₀.2) hr0
  refine ⟨c, hc, fun z hz hfz => ?_⟩
  have h1 : v ((r k).evalAt z) = v (f z₀) := (H z hz).trans h0

  have h2 : v (f z - (r k).evalAt z) < v ((r k).evalAt z) := by
    rw [← Valuation.map_neg, neg_sub, h1]; exact happrox z
  have h3 : v (f z) = v ((r k).evalAt z) := Valuation.map_eq_of_sub_lt _ h2
  rw [hfz, Valuation.map_zero, h1] at h3
  exact hv0 h3.symm

end CerednikDrinfeld.Omega.HolLocNV

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {S : Set K} {f : ↥S → K} (hf : f ∈ CerednikDrinfeld.Omega.holOn K S) (z₀ : ↥S) (hz₀ : f z₀ ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ z : ↥S, Valued.v ((z : K) - (z₀ : K)) < Valued.v c → f z ≠ 0 :=
  CerednikDrinfeld.Omega.HolLocNV.exists_radius_of_isHolOn hf z₀ hz₀

end S_CerednikDrinfeld_Omega_exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn (solution)
