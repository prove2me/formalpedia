-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_v_apply_div_sub_one_lt_of_isUnit_of_mem_stdEdgeTube
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0527e193-eb79-5c2a-950d-535dd836d067

import Definitions.Def_CerednikDrinfeld_OmegaTubes
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_v_apply_div_sub_one_lt_of_isUnit_of_mem_stdEdgeTube

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_v_apply_div_sub_one_lt_of_isUnit_of_mem_stdEdgeTube.CerednikDrinfeld.Omega Polynomial"

noncomputable section

namespace CerednikDrinfeld
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "stdEdgeTube PseudoUniformizer affinoid affinoid_subset_upperHalfPlane mem_affinoid_iff' RatPair RatPair.evalAt vRestrict v_lt_iff_vRestrict_lt tendstoUniformly_iff_vRestrict restrictAffinoid holRing PseudoUniformizer.ϖ upperHalfPlane mem_upperHalfPlane_iff"
namespace AnnulusRes
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

local notation "𝔯" => Valued.v (algebraMap K₀ K (PseudoUniformizer.ϖ ϖ))

theorem r_pos : 0 < 𝔯 := ϖ.pos
theorem r_lt_one : 𝔯 < 1 := ϖ.lt_one

theorem stdEdgeTube_subset_affinoid_one
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 𝔯 ∨ 1 ≤ Valued.v (algebraMap K₀ K a)) :
    stdEdgeTube ϖ ⊆ affinoid ϖ 1 := by
  rintro z ⟨-, h1, h2⟩
  rw [mem_affinoid_iff']
  refine ⟨?_, fun a => ?_⟩
  · rw [pow_one]
    exact h2.le.trans ((one_le_inv₀ (r_pos ϖ)).2 (r_lt_one ϖ).le)
  · rw [pow_one]
    rcases hunif a with ha | ha
    ·
      have hlt : Valued.v (algebraMap K₀ K a) < Valued.v z := ha.trans_lt h1
      rw [Valuation.map_sub_eq_of_lt_left _ hlt]
      exact h1.le
    ·
      have hlt : Valued.v z < Valued.v (algebraMap K₀ K a) := h2.trans_le ha
      rw [Valuation.map_sub_eq_of_lt_right _ hlt]
      exact (r_lt_one ϖ).le.trans ha

theorem v_le_or_one_le_of_not_mem
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 𝔯 ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    {w : K} (hw : w ∉ stdEdgeTube ϖ) : Valued.v w ≤ 𝔯 ∨ 1 ≤ Valued.v w := by
  by_contra h
  rw [not_or, not_le, not_le] at h
  apply hw
  refine ⟨?_, h.1, h.2⟩
  rw [mem_upperHalfPlane_iff]
  rintro a rfl
  rcases hunif a with ha | ha
  · exact not_lt.2 ha h.1
  · exact not_lt.2 ha h.2

theorem v_sub_eq_of_mem_of_not_mem
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 𝔯 ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    {z w : K} (hz : z ∈ stdEdgeTube ϖ) (hw : w ∉ stdEdgeTube ϖ) :
    (Valued.v w ≤ 𝔯 ∧ Valued.v (z - w) = Valued.v z) ∨ (1 ≤ Valued.v w ∧ Valued.v (z - w) = Valued.v w) := by
  rcases v_le_or_one_le_of_not_mem ϖ hunif hw with h | h
  · left
    exact ⟨h, Valuation.map_sub_eq_of_lt_left _ (h.trans_lt hz.2.1)⟩
  · right
    exact ⟨h, Valuation.map_sub_eq_of_lt_right _ (hz.2.2.trans_le h)⟩

omit ϖ in

def PU (x y : K) : Prop := Valued.v (x - y) < Valued.v y

namespace PU

omit ϖ

theorem v_eq {x y : K} (h : PU x y) : Valued.v x = Valued.v y := Valuation.map_eq_of_sub_lt _ h

theorem ne_zero {x y : K} (h : PU x y) : y ≠ 0 := fun hy => by
  rw [PU, hy, sub_zero, Valuation.map_zero] at h; exact not_lt_zero h

theorem refl {y : K} (hy : y ≠ 0) : PU y y := by
  rw [PU, sub_self, Valuation.map_zero]; exact (Valuation.pos_iff _).2 hy

theorem symm {x y : K} (h : PU x y) : PU y x := by
  have := h.v_eq
  rw [PU, ← Valuation.map_neg, neg_sub, this]; exact h

theorem trans {x y z : K} (h : PU x y) (h' : PU y z) : PU x z := by
  have hyz := h'.v_eq
  rw [PU] at h h' ⊢
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]
  exact (Valuation.map_add _ _ _).trans_lt (max_lt (hyz ▸ h) h')

theorem mul {x y x' y' : K} (h : PU x y) (h' : PU x' y') : PU (x * x') (y * y') := by
  have hx := h.v_eq
  rw [PU] at h h' ⊢
  have : x * x' - y * y' = x * (x' - y') + (x - y) * y' := by ring
  rw [this, map_mul]
  refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
  · rw [map_mul, hx]; exact mul_lt_mul_of_pos_left h' ((Valuation.pos_iff _).2 (ne_zero h))
  · rw [map_mul]; exact mul_lt_mul_of_pos_right h ((Valuation.pos_iff _).2 (ne_zero h'))

theorem inv {x y : K} (h : PU x y) : PU x⁻¹ y⁻¹ := by
  have hy := h.ne_zero
  have hx : x ≠ 0 := fun hx => by
    have := h.v_eq; rw [hx, Valuation.map_zero] at this; exact hy ((Valuation.zero_iff _).1 this.symm)
  have hv := h.v_eq
  rw [PU] at h ⊢
  have : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by field_simp
  rw [this, map_div₀, Valuation.map_mul, hv, ← Valuation.map_neg, neg_sub, Valuation.map_inv]
  have hy0 : 0 < Valued.v y := (Valuation.pos_iff _).2 hy
  calc Valued.v (x - y) / (Valued.v y * Valued.v y) < Valued.v y / (Valued.v y * Valued.v y) :=
        div_lt_div_of_pos_right h (mul_pos hy0 hy0)
    _ = (Valued.v y)⁻¹ := by field_simp

theorem div {x y x' y' : K} (h : PU x y) (h' : PU x' y') : PU (x / x') (y / y') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]; exact h.mul h'.inv

theorem of_eq {x y y' : K} (h : PU x y) (e : y = y') : PU x y' := e ▸ h

theorem v_div_sub_one_lt {x y : K} (h : PU x y) : Valued.v (x / y - 1) < 1 := by
  have hy := h.ne_zero
  have : x / y - 1 = (x - y) / y := by field_simp
  rw [this, map_div₀, div_lt_one₀ ((Valuation.pos_iff _).2 hy)]
  exact h

end PU

theorem exists_pu_multiset_prod
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 𝔯 ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (S : Multiset K) (hS : ∀ α ∈ S, α ∉ stdEdgeTube ϖ) :
    ∃ (c : K) (m : ℕ), c ≠ 0 ∧ ∀ z ∈ stdEdgeTube ϖ, PU (S.map (fun α => z - α)).prod (c * z ^ m) := by
  induction S using Multiset.induction_on with
  | empty => exact ⟨1, 0, one_ne_zero, fun z _ => by simpa using PU.refl (one_ne_zero (α := K))⟩
  | cons α S ih =>
    obtain ⟨c, m, hc, h⟩ := ih (fun β hβ => hS β (Multiset.mem_cons_of_mem hβ))
    have hα : α ∉ stdEdgeTube ϖ := hS α (Multiset.mem_cons_self α S)
    rcases v_le_or_one_le_of_not_mem ϖ hunif hα with hsmall | hlarge
    ·
      refine ⟨c, m + 1, hc, fun z hz => ?_⟩
      have h1 : PU (z - α) z := by
        rw [PU, sub_sub_cancel_left, Valuation.map_neg]; exact hsmall.trans_lt hz.2.1
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact (h1.mul (h z hz)).of_eq (by ring)
    ·
      have hα0 : α ≠ 0 := fun h0 => by
        rw [h0, Valuation.map_zero] at hlarge; exact not_le.2 zero_lt_one hlarge
      refine ⟨-α * c, m, mul_ne_zero (neg_ne_zero.2 hα0) hc, fun z hz => ?_⟩
      have h1 : PU (z - α) (-α) := by
        rw [PU, sub_neg_eq_add, sub_add_cancel, Valuation.map_neg]; exact hz.2.2.trans_le hlarge
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact (h1.mul (h z hz)).of_eq (by ring)

theorem exists_pu_eval [IsAlgClosed K]
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 𝔯 ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (p : K[X]) (hp0 : p ≠ 0) (hp : ∀ z ∈ stdEdgeTube ϖ, p.eval z ≠ 0) :
    ∃ (c : K) (m : ℕ), c ≠ 0 ∧ ∀ z ∈ stdEdgeTube ϖ, PU (p.eval z) (c * z ^ m) := by
  have hroots : ∀ α ∈ p.roots, α ∉ stdEdgeTube ϖ := fun α hα hmem => hp α hmem ((mem_roots hp0).1 hα)
  obtain ⟨c, m, hc, h⟩ := exists_pu_multiset_prod ϖ hunif p.roots hroots
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp0
  refine ⟨p.leadingCoeff * c, m, mul_ne_zero hlc hc, fun z hz => ?_⟩
  have hsplit := (IsAlgClosed.splits p).eq_prod_roots
  have hev : p.eval z = p.leadingCoeff * (Multiset.map (fun α => z - α) p.roots).prod := by
    conv_lhs => rw [hsplit]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg _ (Multiset.map_congr rfl fun α _ => ?_)
    simp
  rw [hev]
  exact ((PU.refl hlc).mul (h z hz)).of_eq (by ring)

theorem exists_pu_div [IsAlgClosed K]
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 𝔯 ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (p q : K[X]) (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hp : ∀ z ∈ stdEdgeTube ϖ, p.eval z ≠ 0) (hq : ∀ z ∈ stdEdgeTube ϖ, q.eval z ≠ 0) :
    ∃ (c : K) (m : ℤ), c ≠ 0 ∧ ∀ z ∈ stdEdgeTube ϖ, PU (p.eval z / q.eval z) (c * z ^ m) := by
  obtain ⟨cp, mp, hcp, hP⟩ := exists_pu_eval ϖ hunif p hp0 hp
  obtain ⟨cq, mq, hcq, hQ⟩ := exists_pu_eval ϖ hunif q hq0 hq
  refine ⟨cp / cq, (mp : ℤ) - (mq : ℤ), div_ne_zero hcp hcq, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := fun h0 => by
    have := hz.2.1; rw [h0, Valuation.map_zero] at this; exact not_lt_zero this
  refine ((hP z hz).div (hQ z hz)).of_eq ?_
  rw [zpow_sub₀ hz0, zpow_natCast, zpow_natCast, mul_div_mul_comm]

theorem exists_ratPair_pu (f : ↥(holRing ϖ)) (hf : IsUnit f) (n : ℕ) :
    ∃ r : RatPair K, r.IsPoleFreeOn (affinoid ϖ n) ∧
      ∀ z : ↥(affinoid ϖ n), PU (restrictAffinoid ϖ n (f : ↥(upperHalfPlane K₀ K) → K) z) (r.evalAt z) := by
  obtain ⟨g, hfg⟩ := hf.exists_right_inv
  have hpt : ∀ z : ↥(upperHalfPlane K₀ K),
      (f : ↥(upperHalfPlane K₀ K) → K) z * (g : ↥(upperHalfPlane K₀ K) → K) z = 1 := fun z => by
    have := congrArg (fun h : ↥(holRing ϖ) => (h : ↥(upperHalfPlane K₀ K) → K) z) hfg
    simpa using this
  obtain ⟨r, hr, -, hlim⟩ := f.2 n
  obtain ⟨B, hB⟩ := (g.2 n).bounded
  by_cases hB0 : B = 0
  · refine ⟨r 0, hr 0, fun z => ?_⟩
    have hg0 : (g : ↥(upperHalfPlane K₀ K) → K) (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z) = 0 := by
      have := hB z
      rw [hB0, map_zero, le_zero_iff, map_eq_zero] at this
      exact this
    have := hpt (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z)
    rw [hg0, mul_zero] at this
    exact absurd this zero_ne_one
  have hlow : ∀ z : ↥(affinoid ϖ n), Valued.v B⁻¹ ≤
      Valued.v (restrictAffinoid ϖ n (f : ↥(upperHalfPlane K₀ K) → K) z) := fun z => by
    have h1 := hpt (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z)
    have hgz := hB z
    have hf1 : Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z)) =
        (Valued.v ((g : ↥(upperHalfPlane K₀ K) → K) (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z)))⁻¹ := by
      have := congrArg Valued.v h1
      rw [map_mul, map_one] at this
      exact eq_inv_of_mul_eq_one_left this
    have hgpos : 0 < Valued.v ((g : ↥(upperHalfPlane K₀ K) → K) (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z)) := by
      rw [Valuation.pos_iff]
      intro h0
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1
    change Valued.v B⁻¹ ≤ Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) z))
    rw [hf1, map_inv₀]
    exact inv_anti₀ hgpos hgz
  have hBinv : vRestrict K B⁻¹ ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact inv_ne_zero hB0
  rw [tendstoUniformly_iff_vRestrict] at hlim
  obtain ⟨k, hk⟩ := (hlim (Units.mk0 _ hBinv)).exists
  refine ⟨r k, hr k, fun z => ?_⟩
  have hlt : Valued.v ((r k).evalAt z - restrictAffinoid ϖ n (f : ↥(upperHalfPlane K₀ K) → K) z) < Valued.v B⁻¹ := by
    rw [v_lt_iff_vRestrict_lt]
    exact hk z
  exact PU.symm (hlt.trans_le (hlow z))

end CerednikDrinfeld.Omega.AnnulusRes

end

open CerednikDrinfeld.Omega.AnnulusRes in
theorem solution
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (f : ↥(holRing ϖ)) (hf : IsUnit f) :
    ∃ (c : K) (m : ℤ), c ≠ 0 ∧
      ∀ (z : K) (hz : z ∈ stdEdgeTube ϖ),
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨z, hz.1⟩ / (c * z ^ m) - 1) < 1 ∧
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨z, hz.1⟩) = Valued.v c * Valued.v z ^ m := by
  obtain ⟨r, hr, hrf⟩ := exists_ratPair_pu ϖ f hf 1
  have hsub := stdEdgeTube_subset_affinoid_one ϖ hunif

  have hfr : ∀ (z : K) (hz : z ∈ stdEdgeTube ϖ),
      PU ((f : ↥(upperHalfPlane K₀ K) → K) ⟨z, hz.1⟩) (r.evalAt z) := fun z hz => hrf ⟨z, hsub hz⟩
  have hq : ∀ z ∈ stdEdgeTube ϖ, r.den.eval z ≠ 0 := fun z hz => hr z (hsub hz)
  have hp : ∀ z ∈ stdEdgeTube ϖ, r.num.eval z ≠ 0 := fun z hz h0 =>
    (hfr z hz).ne_zero (by rw [RatPair.evalAt, h0, zero_div])

  by_cases hne : ∃ z, z ∈ stdEdgeTube ϖ
  swap
  · exact ⟨1, 0, one_ne_zero, fun z hz => (hne ⟨z, hz⟩).elim⟩
  obtain ⟨z₁, hz₁⟩ := hne
  have hp0 : r.num ≠ 0 := fun h => hp z₁ hz₁ (by rw [h, eval_zero])
  have hq0 : r.den ≠ 0 := fun h => hq z₁ hz₁ (by rw [h, eval_zero])
  obtain ⟨c, m, hc, hpq⟩ := exists_pu_div ϖ hunif r.num r.den hp0 hq0 hp hq
  refine ⟨c, m, hc, fun z hz => ?_⟩
  have key : PU ((f : ↥(upperHalfPlane K₀ K) → K) ⟨z, hz.1⟩) (c * z ^ m) := (hfr z hz).trans (hpq z hz)
  exact ⟨key.v_div_sub_one_lt, by rw [key.v_eq, map_mul, map_zpow₀]⟩

end S_CerednikDrinfeld_Omega_exists_v_apply_div_sub_one_lt_of_isUnit_of_mem_stdEdgeTube
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_v_apply_div_sub_one_lt_of_isUnit_of_mem_stdEdgeTube (solution)
