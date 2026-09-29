-- Prove2me | solution 1 for Deformation.ProartinianCat.exists_surjective_mvPowerSeriesLift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ba399af8-34f5-50d6-83b8-eddc83b44329

import Mathlib
import Definitions.Def_Deformations_TangentSubmodule
import Definitions.Def_Deformations_MvPowerSeriesObj
import Definitions.Def_Deformations_ProartinianCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_ProartinianCat_exists_surjective_mvPowerSeriesLift

set_option linter.unusedSectionVars false

open scoped DualNumber

universe u

namespace Deformation
p2m_export "Deformation" "ProartinianCat.tangentSubmodule ProartinianCat ProartinianCat.mvPowerSeriesObj"
p2m_open "Deformation"

p2m_open "CategoryTheory IsLocalRing Filter Topology Deformation.ProartinianCat P2MW.S_Deformation_ProartinianCat_exists_surjective_mvPowerSeriesLift.Deformation.ProartinianCat"

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

namespace ProartinianCat
p2m_export "Deformation.ProartinianCat" "residueMap residueMap_add residueMap_algebraMap residueMap_eq_zero_of_mem isLocallyConstant_residueMap IsTangentVector tangentSubmodule mem_tangentSubmodule of Hom toResidueField algebra carrier mk hasEval_of_forall_mem_maximalIdeal mvPowerSeriesObj mvPowerSeriesObjX"
p2m_open "Deformation.ProartinianCat"

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
variable {R : ProartinianCat 𝓞}

namespace IsTangentVector p2m_export "Deformation.ProartinianCat.IsTangentVector" "map_zero map_one map_algebraMap isLocallyConstant mk leibniz map_add" end IsTangentVector
namespace IsTangentVector
p2m_open_scoped "Deformation.ProartinianCat.IsTangentVector" in

private lemma _root_.Deformation.ProartinianCat.IsTangentVector.eq_zero_of_mem_sup {D : R → 𝓴 𝓞} (hD : IsTangentVector R D) {r : R}
    (hr : r ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝓞).map (algebraMap 𝓞 R)) :
    D r = 0 := by

  have key : ∀ x ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝓞).map (algebraMap 𝓞 R),
      x ∈ maximalIdeal R ∧ D x = 0 := by
    have hsmul : ∀ (c x : R), x ∈ maximalIdeal R ∧ D x = 0 → c * x ∈ maximalIdeal R ∧ D (c * x) = 0 := by
      rintro c x ⟨hxm, hDx⟩
      refine ⟨Ideal.mul_mem_left _ c hxm, ?_⟩
      rw [hD.leibniz, hDx, mul_zero, zero_add, residueMap_eq_zero_of_mem hxm, mul_zero]
    have hadd : ∀ (x y : R), (x ∈ maximalIdeal R ∧ D x = 0) → (y ∈ maximalIdeal R ∧ D y = 0) →
        x + y ∈ maximalIdeal R ∧ D (x + y) = 0 := by
      rintro x y ⟨hxm, hDx⟩ ⟨hym, hDy⟩
      exact ⟨add_mem hxm hym, by rw [hD.map_add, hDx, hDy, add_zero]⟩
    have hzero : (0 : R) ∈ maximalIdeal R ∧ D 0 = 0 := ⟨zero_mem _, hD.map_zero⟩
    have hsq : ∀ x ∈ maximalIdeal R ^ 2, x ∈ maximalIdeal R ∧ D x = 0 := by
      intro x hx
      rw [pow_two] at hx
      refine Submodule.mul_induction_on hx (fun r hr s hs => ?_) (fun x y hx hy => hadd x y hx hy)
      refine ⟨Ideal.mul_mem_left _ r hs, ?_⟩
      rw [hD.leibniz, residueMap_eq_zero_of_mem hr, residueMap_eq_zero_of_mem hs, zero_mul,
        mul_zero, add_zero]
    have hmap : ∀ x ∈ (maximalIdeal 𝓞).map (algebraMap 𝓞 R), x ∈ maximalIdeal R ∧ D x = 0 := by
      intro x hx
      refine Submodule.span_induction ?_ hzero (fun x y _ _ hx hy => hadd x y hx hy)
        (fun c x _ hx => ?_) hx
      · rintro _ ⟨o, ho, rfl⟩
        refine ⟨?_, hD.map_algebraMap o⟩
        rw [mem_maximalIdeal, mem_nonunits_iff]
        exact fun h => (mem_maximalIdeal o).mp ho (IsLocalHom.map_nonunit o h)
      · rw [smul_eq_mul]
        exact hsmul c x hx
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    exact hadd a b (hsq a ha) (hmap b hb)
  exact (key r hr).2

end IsTangentVector
p2m_export "Deformation.ProartinianCat" "IsTangentVector.eq_zero_of_mem_sup"
variable (R) in

structure IsCotangentFunctional (δ : R → 𝓴 𝓞) : Prop where
  map_add : ∀ r s, δ (r + s) = δ r + δ s
  map_algebraMap_mul : ∀ (o : 𝓞) (r : R),
    δ (algebraMap 𝓞 R o * r) = algebraMap 𝓞 (𝓴 𝓞) o * δ r
  eq_zero_of_mem_sup : ∀ r ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝓞).map (algebraMap 𝓞 R),
    δ r = 0
  exists_isOpen_eq_zero : ∃ J : Ideal R, IsOpen (J : Set R) ∧ ∀ r ∈ J, δ r = 0

lemma IsCotangentFunctional.of_exists_isOpen_le
    (hopen : ∃ J : Ideal R, IsOpen (J : Set R) ∧
      J ≤ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝓞).map (algebraMap 𝓞 R))
    {δ : R → 𝓴 𝓞} (h1 : ∀ r s, δ (r + s) = δ r + δ s)
    (h2 : ∀ (o : 𝓞) (r : R), δ (algebraMap 𝓞 R o * r) = algebraMap 𝓞 (𝓴 𝓞) o * δ r)
    (h3 : ∀ r ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝓞).map (algebraMap 𝓞 R), δ r = 0) :
    IsCotangentFunctional R δ where
  map_add := h1
  map_algebraMap_mul := h2
  eq_zero_of_mem_sup := h3
  exists_isOpen_eq_zero := by
    obtain ⟨J, hJopen, hJle⟩ := hopen
    exact ⟨J, hJopen, fun r hr => h3 r (hJle hr)⟩

namespace IsTangentVector
p2m_open_scoped "Deformation.ProartinianCat.IsTangentVector" in

private lemma _root_.Deformation.ProartinianCat.IsTangentVector.exists_isOpen_eq_zero {D : R → 𝓴 𝓞} (hD : IsTangentVector R D) :
    ∃ J : Ideal R, IsOpen (J : Set R) ∧ ∀ r ∈ J, D r = 0 := by
  have hopen : IsOpen {x : R | D x = 0} := hD.isLocallyConstant.isOpen_fiber 0
  have hmem : {x : R | D x = 0} ∈ nhds (0 : R) := hopen.mem_nhds hD.map_zero
  obtain ⟨J, hJopen, hJsub⟩ := (IsLinearTopology.hasBasis_open_ideal.mem_iff).mp hmem
  exact ⟨J, hJopen, fun r hr => hJsub hr⟩

end IsTangentVector
p2m_export "Deformation.ProartinianCat" "IsTangentVector.exists_isOpen_eq_zero"
namespace IsTangentVector
p2m_open_scoped "Deformation.ProartinianCat.IsTangentVector" in

private lemma _root_.Deformation.ProartinianCat.IsTangentVector.isCotangentFunctional {D : R → 𝓴 𝓞} (hD : IsTangentVector R D) :
    IsCotangentFunctional R D where
  map_add := hD.map_add
  map_algebraMap_mul o r := by
    rw [hD.leibniz, hD.map_algebraMap, zero_mul, add_zero, residueMap_algebraMap]
  eq_zero_of_mem_sup _ hr := hD.eq_zero_of_mem_sup hr
  exists_isOpen_eq_zero := hD.exists_isOpen_eq_zero

end IsTangentVector
p2m_export "Deformation.ProartinianCat" "IsTangentVector.isCotangentFunctional"
namespace IsCotangentFunctional

variable {δ : R → 𝓴 𝓞} (hδ : IsCotangentFunctional R δ)

include hδ

lemma map_zero : δ 0 = 0 := by
  have h := (hδ.map_add 0 0).symm
  rw [add_zero] at h
  exact add_left_cancel (h.trans (add_zero (δ 0)).symm)

lemma map_neg (r : R) : δ (-r) = -δ r := by
  have h := hδ.map_add r (-r)
  rw [add_neg_cancel, hδ.map_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

lemma map_sub (r s : R) : δ (r - s) = δ r - δ s := by
  rw [sub_eq_add_neg, hδ.map_add, hδ.map_neg, ← sub_eq_add_neg]

lemma map_algebraMap (o : 𝓞) : δ (algebraMap 𝓞 R o) = algebraMap 𝓞 (𝓴 𝓞) o * δ 1 := by
  simpa using hδ.map_algebraMap_mul o 1

lemma eq_zero_of_mem_pow {r : R} (hr : r ∈ maximalIdeal R ^ 2) : δ r = 0 :=
  hδ.eq_zero_of_mem_sup r (Submodule.mem_sup_left hr)

lemma isLocallyConstant : IsLocallyConstant δ := by
  obtain ⟨J, hJopen, hJ⟩ := hδ.exists_isOpen_eq_zero
  rw [IsLocallyConstant.iff_exists_open]
  intro r
  refine ⟨(fun y => y - r) ⁻¹' J, (continuous_id.sub continuous_const).isOpen_preimage _ hJopen,
    by simp, fun y hy => ?_⟩
  rw [show δ y = δ (r + (y - r)) from congrArg δ (by ring), hδ.map_add, hJ _ hy, add_zero]

lemma sub_residueMap_mul_eq {r : R} {o : 𝓞} (ho : r - algebraMap 𝓞 R o ∈ maximalIdeal R) :
    δ r - residueMap R r * δ 1 = δ (r - algebraMap 𝓞 R o) := by
  have hres : residueMap R r = algebraMap 𝓞 (𝓴 𝓞) o := by
    have h0 : residueMap R (r - algebraMap 𝓞 R o) = 0 := residueMap_eq_zero_of_mem ho
    have h1 : residueMap R (r - algebraMap 𝓞 R o)
        = residueMap R r - residueMap R (algebraMap 𝓞 R o) :=
      _root_.map_sub (toResidueField R).hom r (algebraMap 𝓞 R o)
    rw [h1, residueMap_algebraMap, sub_eq_zero] at h0
    exact h0
  rw [hδ.map_sub, hδ.map_algebraMap, hres]

theorem isTangentVector : IsTangentVector R (fun r => δ r - residueMap R r * δ 1) where
  map_add r s := by
    show δ (r + s) - residueMap R (r + s) * δ 1
      = (δ r - residueMap R r * δ 1) + (δ s - residueMap R s * δ 1)
    rw [hδ.map_add, residueMap_add]
    ring
  leibniz r s := by
    show δ (r * s) - residueMap R (r * s) * δ 1
      = residueMap R r * (δ s - residueMap R s * δ 1)
        + (δ r - residueMap R r * δ 1) * residueMap R s
    obtain ⟨a, ha⟩ := IsResidueAlgebra.exists_sub_mem_maximalIdeal 𝓞 r
    obtain ⟨b, hb⟩ := IsResidueAlgebra.exists_sub_mem_maximalIdeal 𝓞 s

    have hresr : residueMap R r = algebraMap 𝓞 (𝓴 𝓞) a := by
      have h0 : residueMap R (r - algebraMap 𝓞 R a) = 0 := residueMap_eq_zero_of_mem ha
      rw [show residueMap R (r - algebraMap 𝓞 R a)
            = residueMap R r - residueMap R (algebraMap 𝓞 R a) from
          _root_.map_sub (toResidueField R).hom r (algebraMap 𝓞 R a),
        residueMap_algebraMap, sub_eq_zero] at h0
      exact h0
    have hress : residueMap R s = algebraMap 𝓞 (𝓴 𝓞) b := by
      have h0 : residueMap R (s - algebraMap 𝓞 R b) = 0 := residueMap_eq_zero_of_mem hb
      rw [show residueMap R (s - algebraMap 𝓞 R b)
            = residueMap R s - residueMap R (algebraMap 𝓞 R b) from
          _root_.map_sub (toResidueField R).hom s (algebraMap 𝓞 R b),
        residueMap_algebraMap, sub_eq_zero] at h0
      exact h0

    have hdecomp : r * s - algebraMap 𝓞 R (a * b)
        = algebraMap 𝓞 R a * (s - algebraMap 𝓞 R b)
          + algebraMap 𝓞 R b * (r - algebraMap 𝓞 R a)
          + (r - algebraMap 𝓞 R a) * (s - algebraMap 𝓞 R b) := by
      rw [map_mul]
      ring
    have hmem : r * s - algebraMap 𝓞 R (a * b) ∈ maximalIdeal R := by
      rw [hdecomp]
      exact add_mem (add_mem (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_left _ _ ha))
        (Ideal.mul_mem_left _ _ hb)
    have hsq : (r - algebraMap 𝓞 R a) * (s - algebraMap 𝓞 R b) ∈ maximalIdeal R ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul ha hb

    rw [hδ.sub_residueMap_mul_eq hmem, hδ.sub_residueMap_mul_eq ha, hδ.sub_residueMap_mul_eq hb,
      hdecomp, hδ.map_add, hδ.map_add, hδ.map_algebraMap_mul, hδ.map_algebraMap_mul,
      hδ.eq_zero_of_mem_pow hsq, add_zero, hresr, hress]
    ring
  map_algebraMap o := by
    show δ (algebraMap 𝓞 R o) - residueMap R (algebraMap 𝓞 R o) * δ 1 = 0
    rw [hδ.map_algebraMap, residueMap_algebraMap, sub_self]
  isLocallyConstant :=
    IsLocallyConstant.comp₂ hδ.isLocallyConstant isLocallyConstant_residueMap
      fun x y => x - y * δ 1

omit hδ in

lemma sub_residueMap_mul_eq_of_mem {r : R} (hr : r ∈ maximalIdeal R) :
    δ r - residueMap R r * δ 1 = δ r := by
  rw [residueMap_eq_zero_of_mem hr, zero_mul, sub_zero]

end IsCotangentFunctional

theorem isTangentVector_iff_isCotangentFunctional {D : R → 𝓴 𝓞} :
    IsTangentVector R D ↔ IsCotangentFunctional R D ∧ D 1 = 0 := by
  constructor
  · exact fun hD => ⟨hD.isCotangentFunctional, hD.map_one⟩
  · rintro ⟨hδ, h1⟩
    have key : (fun r => D r - residueMap R r * D 1) = D := by
      funext r
      rw [h1, mul_zero, sub_zero]
    exact key ▸ hδ.isTangentVector

lemma algebraMap_mem_maximalIdeal_of_mem {o : 𝓞} (ho : o ∈ maximalIdeal 𝓞) :
    algebraMap 𝓞 R o ∈ maximalIdeal R := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  exact fun h => (mem_maximalIdeal o).mp ho (IsLocalHom.map_nonunit o h)

lemma exists_mem_maximalIdeal_sub_algebraMap_mem_pow_two {x : R}
    (hx : x ∈ (maximalIdeal 𝓞).map (algebraMap 𝓞 R)) :
    ∃ o ∈ maximalIdeal 𝓞, x - algebraMap 𝓞 R o ∈ maximalIdeal R ^ 2 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨o, ho, rfl⟩
    exact ⟨o, ho, by simp⟩
  · exact ⟨0, zero_mem _, by simp⟩
  · rintro x y _ _ ⟨o, ho, hxo⟩ ⟨p, hp, hyp⟩
    refine ⟨o + p, add_mem ho hp, ?_⟩
    have hsplit : x + y - algebraMap 𝓞 R (o + p)
        = (x - algebraMap 𝓞 R o) + (y - algebraMap 𝓞 R p) := by
      rw [map_add]; ring
    rw [hsplit]
    exact add_mem hxo hyp
  · rintro a x _ ⟨o, ho, hxo⟩

    have hxm : x ∈ maximalIdeal R := by
      have hx' : x = algebraMap 𝓞 R o + (x - algebraMap 𝓞 R o) := by ring
      rw [hx']
      exact add_mem (algebraMap_mem_maximalIdeal_of_mem ho)
        (Ideal.pow_le_self two_ne_zero hxo)

    obtain ⟨a', ha'⟩ := IsResidueAlgebra.exists_sub_mem_maximalIdeal 𝓞 a
    refine ⟨a' * o, Ideal.mul_mem_left _ _ ho, ?_⟩
    have hdecomp : a • x - algebraMap 𝓞 R (a' * o)
        = (a - algebraMap 𝓞 R a') * x + algebraMap 𝓞 R a' * (x - algebraMap 𝓞 R o) := by
      rw [smul_eq_mul, map_mul]; ring
    rw [hdecomp]
    refine add_mem ?_ (Ideal.mul_mem_left _ _ hxo)
    rw [pow_two]
    exact Ideal.mul_mem_mul ha' hxm

section Nakayama

variable (A : Subalgebra 𝓞 R)
variable (hgen : ∀ y ∈ maximalIdeal R, ∃ a ∈ A, y - a ∈ maximalIdeal R ^ 2)

include hgen

omit [IsLocalRing 𝓞]

lemma exists_sub_mem_pow_succ_of_mem_pow_succ :
    ∀ n : ℕ, ∀ y ∈ maximalIdeal R ^ (n + 1),
      ∃ a ∈ A, a ∈ maximalIdeal R ^ (n + 1) ∧ y - a ∈ maximalIdeal R ^ (n + 2) := by
  intro n
  induction n with
  | zero =>
    intro y hy
    have hy' : y ∈ maximalIdeal R := by simpa using hy
    obtain ⟨a, haA, hya⟩ := hgen y hy'

    have ham : a ∈ maximalIdeal R := by
      have ha : a = y - (y - a) := by ring
      rw [ha]
      exact sub_mem hy' (Ideal.pow_le_self two_ne_zero hya)
    exact ⟨a, haA, by simpa using ham, by simpa using hya⟩
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro x hx z hz
      obtain ⟨a, haA, ham, hxa⟩ := ih x hx
      obtain ⟨b, hbA, hzb⟩ := hgen z hz
      have hbm : b ∈ maximalIdeal R := by
        have hb : b = z - (z - b) := by ring
        rw [hb]
        exact sub_mem hz (Ideal.pow_le_self two_ne_zero hzb)
      refine ⟨a * b, mul_mem haA hbA, ?_, ?_⟩
      · rw [pow_succ]
        exact Ideal.mul_mem_mul ham hbm
      · have hdecomp : x * z - a * b = (x - a) * z + a * (z - b) := by ring
        rw [hdecomp]
        refine add_mem ?_ ?_
        ·
          rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
          exact Ideal.mul_mem_mul hxa hz
        ·
          rw [pow_add]
          exact Ideal.mul_mem_mul ham hzb
    · rintro w₁ w₂ ⟨a, haA, ham, hw₁⟩ ⟨b, hbA, hbm, hw₂⟩
      refine ⟨a + b, add_mem haA hbA, add_mem ham hbm, ?_⟩
      have hsplit : w₁ + w₂ - (a + b) = (w₁ - a) + (w₂ - b) := by ring
      rw [hsplit]
      exact add_mem hw₁ hw₂

lemma exists_sub_mem_pow (n : ℕ) (r : R) :
    ∃ a ∈ A, r - a ∈ maximalIdeal R ^ (n + 1) := by
  induction n with
  | zero =>
    obtain ⟨o, ho⟩ := IsResidueAlgebra.exists_sub_mem_maximalIdeal 𝓞 r
    exact ⟨algebraMap 𝓞 R o, A.algebraMap_mem o, by simpa using ho⟩
  | succ n ih =>
    obtain ⟨a, haA, hra⟩ := ih
    obtain ⟨b, hbA, _, hb⟩ := exists_sub_mem_pow_succ_of_mem_pow_succ A hgen n (r - a) hra
    refine ⟨a + b, add_mem haA hbA, ?_⟩
    have hsplit : r - (a + b) = r - a - b := by ring
    rw [hsplit]
    exact hb

lemma exists_sub_mem_of_isOpen {J : Ideal R} (hJ : IsOpen (J : Set R)) (r : R) :
    ∃ a ∈ A, r - a ∈ J := by
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isProartinian J hJ
  obtain ⟨a, haA, hra⟩ := exists_sub_mem_pow A hgen n r
  exact ⟨a, haA, hn (Ideal.pow_le_pow_right (Nat.le_succ n) hra)⟩

lemma dense_of_forall_exists_sub_mem_pow_two : Dense (A : Set R) := by
  intro r
  have hbasis : (𝓝 r).HasBasis (fun J : Ideal R => IsOpen (J : Set R))
      (fun J : Ideal R => (r + ·) '' (J : Set R)) := by
    rw [← map_add_left_nhds_zero r]
    exact IsLinearTopology.hasBasis_open_ideal.map _
  rw [mem_closure_iff_nhds_basis hbasis]
  intro J hJ
  obtain ⟨a, haA, hra⟩ := exists_sub_mem_of_isOpen A hgen hJ r
  refine ⟨a, haA, a - r, ?_, by ring⟩
  have hneg : a - r = -(r - a) := by ring
  rw [hneg]
  exact neg_mem hra

theorem eq_top_of_isClosed_of_forall_exists_sub_mem_pow_two (hA : IsClosed (A : Set R)) :
    A = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  show x ∈ (A : Set R)
  rw [← hA.closure_eq]
  exact dense_of_forall_exists_sub_mem_pow_two A hgen x

end Nakayama

theorem eq_top_of_isClosed_of_forall_exists_sub_mem_sup (A : Subalgebra 𝓞 R)
    (hA : IsClosed (A : Set R))
    (hgen : ∀ y ∈ maximalIdeal R, ∃ a ∈ A,
      y - a ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝓞).map (algebraMap 𝓞 R)) :
    A = ⊤ := by
  refine eq_top_of_isClosed_of_forall_exists_sub_mem_pow_two A ?_ hA
  intro y hy
  obtain ⟨a, haA, hya⟩ := hgen y hy
  obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hya
  obtain ⟨o, -, hwo⟩ := exists_mem_maximalIdeal_sub_algebraMap_mem_pow_two hw
  refine ⟨a + algebraMap 𝓞 R o, add_mem haA (A.algebraMap_mem o), ?_⟩
  have hkey : y - (a + algebraMap 𝓞 R o) = z + (w - algebraMap 𝓞 R o) := by
    have hy' : y = a + (z + w) := by rw [hzw]; ring
    rw [hy']; ring
  rw [hkey]
  exact add_mem hz hwo

theorem topologicalClosure_adjoin_eq_top (s : Set R)
    (hgen : ∀ y ∈ maximalIdeal R, ∃ a ∈ Submodule.span 𝓞 s,
      y - a ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝓞).map (algebraMap 𝓞 R)) :
    (Algebra.adjoin 𝓞 s).topologicalClosure = ⊤ := by
  refine eq_top_of_isClosed_of_forall_exists_sub_mem_sup _
    (Subalgebra.isClosed_topologicalClosure _) ?_
  intro y hy
  obtain ⟨a, haspan, hya⟩ := hgen y hy
  refine ⟨a, ?_, hya⟩
  refine (Algebra.adjoin 𝓞 s).le_topologicalClosure ?_

  refine Submodule.span_induction (fun x hx => Algebra.subset_adjoin hx) (zero_mem _)
    (fun x y _ _ hx hy => add_mem hx hy) (fun c x _ hx => ?_) haspan
  exact Subalgebra.smul_mem _ hx c

theorem topologicalClosure_adjoin_range_eq_top {d : ℕ} (x : Fin d → R)
    (hgen : ∀ y ∈ maximalIdeal R, ∃ c : Fin d → 𝓞,
      y - ∑ i, c i • x i ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝓞).map (algebraMap 𝓞 R)) :
    (Algebra.adjoin 𝓞 (Set.range x)).topologicalClosure = ⊤ := by
  refine topologicalClosure_adjoin_eq_top _ ?_
  intro y hy
  obtain ⟨c, hc⟩ := hgen y hy
  exact ⟨∑ i, c i • x i,
    sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), hc⟩

theorem exists_isTangentVector_apply_ne_zero {K : Ideal R}
    (hKle : maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝓞).map (algebraMap 𝓞 R) ≤ K)
    {J : Ideal R} (hJ : IsOpen (J : Set R)) (hJK : J ≤ K)
    {z : R} (hzm : z ∈ maximalIdeal R) (hz : z ∉ K) :
    ∃ D : R → 𝓴 𝓞, IsTangentVector R D ∧ D z ≠ 0 := by

  have htor : Module.IsTorsionBySet 𝓞 (R ⧸ (K.restrictScalars 𝓞))
      (maximalIdeal 𝓞 : Set 𝓞) := by
    rw [Module.isTorsionBySet_quotient_iff]
    intro x o ho
    show o • x ∈ K
    rw [Algebra.smul_def]
    exact hKle (Submodule.mem_sup_right
      (Ideal.mul_mem_right x _ (Ideal.mem_map_of_mem _ ho)))
  letI : Module (𝓴 𝓞) (R ⧸ (K.restrictScalars 𝓞)) := htor.module

  have hz0 : (Submodule.Quotient.mk z : R ⧸ (K.restrictScalars 𝓞)) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hz
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero (𝓴 𝓞) hz0

  have hδ : IsCotangentFunctional R
      (fun r => ψ (Submodule.Quotient.mk (p := K.restrictScalars 𝓞) r)) := by
    refine ⟨fun r s => ?_, fun o r => ?_, fun r hr => ?_, ⟨J, hJ, fun r hr => ?_⟩⟩
    · rw [← map_add ψ, ← Submodule.Quotient.mk_add]
    ·
      have h1 : (Submodule.Quotient.mk (p := K.restrictScalars 𝓞) (algebraMap 𝓞 R o * r))
          = algebraMap 𝓞 (𝓴 𝓞) o • (Submodule.Quotient.mk r : R ⧸ (K.restrictScalars 𝓞)) := by
        rw [← Algebra.smul_def, Submodule.Quotient.mk_smul]
        exact (Module.IsTorsionBySet.mk_smul htor o (Submodule.Quotient.mk r)).symm
      rw [h1, map_smul, smul_eq_mul]
    · rw [show (Submodule.Quotient.mk (p := K.restrictScalars 𝓞) r) = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr (hKle hr), map_zero]
    · rw [show (Submodule.Quotient.mk (p := K.restrictScalars 𝓞) r) = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr (hJK hr), map_zero]

  refine ⟨_, hδ.isTangentVector, ?_⟩
  show ψ (Submodule.Quotient.mk z) - residueMap R z * ψ (Submodule.Quotient.mk 1) ≠ 0
  rw [residueMap_eq_zero_of_mem hzm, zero_mul, sub_zero]
  exact hψ

section NakayamaOpen

variable (A : Subalgebra 𝓞 R)

section Absolute

variable (hgen : ∀ y ∈ maximalIdeal R, ∀ J : Ideal R, IsOpen (J : Set R) → J ≠ ⊤ →
  ∃ a ∈ A, y - a ∈ maximalIdeal R ^ 2 ⊔ J)

include hgen

omit [IsLocalRing 𝓞]

lemma exists_sub_mem_pow_succ_sup_of_mem_pow_succ {J : Ideal R} (hJ : IsOpen (J : Set R))
    (hJtop : J ≠ ⊤) :
    ∀ n : ℕ, ∀ y ∈ maximalIdeal R ^ (n + 1),
      ∃ a ∈ A, a ∈ maximalIdeal R ^ (n + 1) ∧ y - a ∈ maximalIdeal R ^ (n + 2) ⊔ J := by
  have hJle : J ≤ maximalIdeal R := le_maximalIdeal hJtop
  have hsuple : maximalIdeal R ^ 2 ⊔ J ≤ maximalIdeal R :=
    sup_le (Ideal.pow_le_self two_ne_zero) hJle
  intro n
  induction n with
  | zero =>
    intro y hy
    have hy' : y ∈ maximalIdeal R := by simpa using hy
    obtain ⟨a, haA, hya⟩ := hgen y hy' J hJ hJtop
    have ham : a ∈ maximalIdeal R := by
      have ha : a = y - (y - a) := by ring
      rw [ha]
      exact sub_mem hy' (hsuple hya)
    exact ⟨a, haA, by simpa using ham, by simpa using hya⟩
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro x hx z hz
      obtain ⟨a, haA, ham, hxa⟩ := ih x hx
      obtain ⟨b, hbA, hzb⟩ := hgen z hz J hJ hJtop
      have hbm : b ∈ maximalIdeal R := by
        have hb : b = z - (z - b) := by ring
        rw [hb]
        exact sub_mem hz (hsuple hzb)
      refine ⟨a * b, mul_mem haA hbA, ?_, ?_⟩
      · rw [pow_succ]
        exact Ideal.mul_mem_mul ham hbm
      · have hdecomp : x * z - a * b = (x - a) * z + a * (z - b) := by ring
        rw [hdecomp]
        refine add_mem ?_ ?_
        ·
          obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hxa
          rw [← huv, add_mul]
          refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
          · rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
            exact Ideal.mul_mem_mul hu hz
          · exact Ideal.mul_mem_right z J hv
        ·
          obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hzb
          rw [← huv, mul_add]
          refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
          · rw [pow_add]
            exact Ideal.mul_mem_mul ham hu
          · exact Ideal.mul_mem_left J a hv
    · rintro w₁ w₂ ⟨a, haA, ham, hw₁⟩ ⟨b, hbA, hbm, hw₂⟩
      refine ⟨a + b, add_mem haA hbA, add_mem ham hbm, ?_⟩
      have hsplit : w₁ + w₂ - (a + b) = (w₁ - a) + (w₂ - b) := by ring
      rw [hsplit]
      exact add_mem hw₁ hw₂

lemma exists_sub_mem_pow_sup {J : Ideal R} (hJ : IsOpen (J : Set R)) (hJtop : J ≠ ⊤)
    (n : ℕ) (r : R) :
    ∃ a ∈ A, r - a ∈ maximalIdeal R ^ (n + 1) ⊔ J := by
  induction n with
  | zero =>
    obtain ⟨o, ho⟩ := IsResidueAlgebra.exists_sub_mem_maximalIdeal 𝓞 r
    exact ⟨algebraMap 𝓞 R o, A.algebraMap_mem o, Submodule.mem_sup_left (by simpa using ho)⟩
  | succ n ih =>
    obtain ⟨a, haA, hra⟩ := ih
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hra
    obtain ⟨b, hbA, -, hb⟩ :=
      exists_sub_mem_pow_succ_sup_of_mem_pow_succ A hgen hJ hJtop n u hu
    refine ⟨a + b, add_mem haA hbA, ?_⟩
    have hsplit : r - (a + b) = (u - b) + v := by
      have h : r - (a + b) = (u + v) - b := by rw [huv]; ring
      rw [h]; ring
    rw [hsplit]
    exact add_mem hb (Submodule.mem_sup_right hv)

lemma exists_sub_mem_of_isOpen_carrying (r : R) {J : Ideal R} (hJ : IsOpen (J : Set R)) :
    ∃ a ∈ A, r - a ∈ J := by
  by_cases hJtop : J = ⊤
  · exact ⟨0, zero_mem A, by simp [hJtop]⟩
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isProartinian J hJ
  obtain ⟨a, haA, hra⟩ := exists_sub_mem_pow_sup A hgen hJ hJtop n r
  exact ⟨a, haA,
    (sup_le ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn) le_rfl) hra⟩

lemma dense_of_forall_isOpen_exists_sub_mem : Dense (A : Set R) := by
  intro r
  have hbasis : (𝓝 r).HasBasis (fun J : Ideal R => IsOpen (J : Set R))
      (fun J : Ideal R => (r + ·) '' (J : Set R)) := by
    rw [← map_add_left_nhds_zero r]
    exact IsLinearTopology.hasBasis_open_ideal.map _
  rw [mem_closure_iff_nhds_basis hbasis]
  intro J hJ
  obtain ⟨a, haA, hra⟩ := exists_sub_mem_of_isOpen_carrying A hgen r hJ
  refine ⟨a, haA, a - r, ?_, by ring⟩
  have hneg : a - r = -(r - a) := by ring
  rw [hneg]
  exact neg_mem hra

theorem eq_top_of_isClosed_of_forall_isOpen_exists_sub_mem (hA : IsClosed (A : Set R)) :
    A = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  show x ∈ (A : Set R)
  rw [← hA.closure_eq]
  exact dense_of_forall_isOpen_exists_sub_mem A hgen x

end Absolute

theorem eq_top_of_isClosed_of_forall_isOpen_exists_sub_mem_sup (hA : IsClosed (A : Set R))
    (hgen : ∀ y ∈ maximalIdeal R, ∀ J : Ideal R, IsOpen (J : Set R) → J ≠ ⊤ → ∃ a ∈ A,
      y - a ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝓞).map (algebraMap 𝓞 R) ⊔ J) :
    A = ⊤ := by
  refine eq_top_of_isClosed_of_forall_isOpen_exists_sub_mem A ?_ hA
  intro y hy J hJ hJtop
  obtain ⟨a, haA, hya⟩ := hgen y hy J hJ hJtop
  obtain ⟨w, hw, j, hj, hwj⟩ := Submodule.mem_sup.mp hya
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hw
  obtain ⟨o, -, hto⟩ := exists_mem_maximalIdeal_sub_algebraMap_mem_pow_two ht
  refine ⟨a + algebraMap 𝓞 R o, add_mem haA (A.algebraMap_mem o), ?_⟩
  have hkey : y - (a + algebraMap 𝓞 R o) = (s + (t - algebraMap 𝓞 R o)) + j := by
    have hy' : y = a + ((s + t) + j) := by rw [hst, hwj]; ring
    rw [hy']; ring
  rw [hkey]
  exact add_mem (Submodule.mem_sup_left (add_mem hs hto)) (Submodule.mem_sup_right hj)

end NakayamaOpen

theorem topologicalClosure_adjoin_eq_top_of_forall_isOpen (s : Set R)
    (hgen : ∀ y ∈ maximalIdeal R, ∀ J : Ideal R, IsOpen (J : Set R) → J ≠ ⊤ →
      ∃ a ∈ Submodule.span 𝓞 s,
        y - a ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝓞).map (algebraMap 𝓞 R) ⊔ J) :
    (Algebra.adjoin 𝓞 s).topologicalClosure = ⊤ := by
  refine eq_top_of_isClosed_of_forall_isOpen_exists_sub_mem_sup _
    (Subalgebra.isClosed_topologicalClosure _) ?_
  intro y hy J hJ hJtop
  obtain ⟨a, haspan, hya⟩ := hgen y hy J hJ hJtop
  refine ⟨a, ?_, hya⟩
  refine (Algebra.adjoin 𝓞 s).le_topologicalClosure ?_
  refine Submodule.span_induction (fun x hx => Algebra.subset_adjoin hx) (zero_mem _)
    (fun x y _ _ hx hy => add_mem hx hy) (fun c x _ hx => ?_) haspan
  exact Subalgebra.smul_mem _ hx c

theorem topologicalClosure_adjoin_range_eq_top_of_forall_isOpen {d : ℕ} (x : Fin d → R)
    (hgen : ∀ y ∈ maximalIdeal R, ∃ c : Fin d → 𝓞, ∀ J : Ideal R,
      IsOpen (J : Set R) → J ≠ ⊤ →
      y - ∑ i, c i • x i ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝓞).map (algebraMap 𝓞 R) ⊔ J) :
    (Algebra.adjoin 𝓞 (Set.range x)).topologicalClosure = ⊤ := by
  refine topologicalClosure_adjoin_eq_top_of_forall_isOpen _ ?_
  intro y hy J hJ hJtop
  obtain ⟨c, hc⟩ := hgen y hy
  exact ⟨∑ i, c i • x i,
    sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), hc J hJ hJtop⟩

section DualBasis

variable {d : ℕ} {Dfam : Fin d → R → 𝓴 𝓞}

variable (Dfam) in

def evalSubmodule (hD : ∀ i, IsTangentVector R (Dfam i)) :
    Submodule (𝓴 𝓞) (Fin d → 𝓴 𝓞) where
  carrier := {v | ∃ y ∈ maximalIdeal R, ∀ i, v i = Dfam i y}
  zero_mem' := ⟨0, zero_mem _, fun i => ((hD i).map_zero).symm⟩
  add_mem' := by
    rintro v w ⟨y, hy, hvy⟩ ⟨y', hy', hvy'⟩
    refine ⟨y + y', add_mem hy hy', fun i => ?_⟩
    rw [Pi.add_apply, hvy i, hvy' i, (hD i).map_add]
  smul_mem' := by
    rintro c v ⟨y, hy, hvy⟩
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (R := 𝓞) c
    refine ⟨algebraMap 𝓞 R o * y, Ideal.mul_mem_left _ _ hy, fun i => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, hvy i,
      (hD i).isCotangentFunctional.map_algebraMap_mul o y,
      show algebraMap 𝓞 (𝓴 𝓞) o = residue 𝓞 o from rfl, ho]

lemma mem_evalSubmodule {hD : ∀ i, IsTangentVector R (Dfam i)} {v : Fin d → 𝓴 𝓞} :
    v ∈ evalSubmodule Dfam hD ↔ ∃ y ∈ maximalIdeal R, ∀ i, v i = Dfam i y :=
  Iff.rfl

lemma exists_eval_eq_sum (hD : ∀ i, IsTangentVector R (Dfam i)) :
    ∃ (n : ℕ) (x : Fin n → R), n ≤ d ∧ (∀ j, x j ∈ maximalIdeal R) ∧
      ∀ y ∈ maximalIdeal R, ∃ c : Fin n → 𝓞, ∀ i,
        Dfam i y = ∑ j, algebraMap 𝓞 (𝓴 𝓞) (c j) * Dfam i (x j) := by
  classical

  have hVfin : Module.Finite (𝓴 𝓞) (evalSubmodule Dfam hD) := by
    have : Module.Finite (𝓴 𝓞) (Fin d → 𝓴 𝓞) := inferInstance
    infer_instance

  have hnd : Module.finrank (𝓴 𝓞) (evalSubmodule Dfam hD) ≤ d := by
    have h1 := Submodule.finrank_le (evalSubmodule Dfam hD)
    rwa [Module.finrank_fin_fun] at h1
  set n := Module.finrank (𝓴 𝓞) (evalSubmodule Dfam hD) with hn
  let b : Module.Basis (Fin n) (𝓴 𝓞) (evalSubmodule Dfam hD) :=
    Module.finBasis (𝓴 𝓞) (evalSubmodule Dfam hD)

  choose xb hxbm hxbv using fun k : Fin n => mem_evalSubmodule.mp (b k).2
  refine ⟨n, xb, hnd, hxbm, ?_⟩
  intro y hy

  have hyV : (fun i => Dfam i y) ∈ evalSubmodule Dfam hD := ⟨y, hy, fun _ => rfl⟩
  choose co hco using fun k : Fin n =>
    IsLocalRing.residue_surjective (R := 𝓞) (b.repr ⟨fun i => Dfam i y, hyV⟩ k)
  refine ⟨co, fun i => ?_⟩

  have hsum : ∑ k, b.repr ⟨fun i => Dfam i y, hyV⟩ k • ((b k : Fin d → 𝓴 𝓞)) =
      fun i => Dfam i y := by
    have h1 := b.sum_repr ⟨fun i => Dfam i y, hyV⟩
    have h2 := congrArg ((evalSubmodule Dfam hD).subtype) h1
    rw [map_sum] at h2
    simpa using h2
  have hi := congrFun hsum i
  rw [Finset.sum_apply] at hi
  rw [← hi]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, hxbv k i,
    show algebraMap 𝓞 (𝓴 𝓞) (co k) = residue 𝓞 (co k) from rfl, hco k]

lemma sub_sum_smul_mem_sup (hD : ∀ i, IsTangentVector R (Dfam i))
    (hspan : ∀ D : R → 𝓴 𝓞, IsTangentVector R D →
      D ∈ Submodule.span (𝓴 𝓞) (Set.range Dfam))
    {n : ℕ} {x : Fin n → R} (hxm : ∀ j, x j ∈ maximalIdeal R)
    {y : R} (hy : y ∈ maximalIdeal R) {c : Fin n → 𝓞}
    (hc : ∀ i, Dfam i y = ∑ j, algebraMap 𝓞 (𝓴 𝓞) (c j) * Dfam i (x j))
    {J : Ideal R} (hJ : IsOpen (J : Set R)) :
    y - ∑ j, c j • x j ∈
      maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝓞).map (algebraMap 𝓞 R) ⊔ J := by

  have hzm : y - ∑ j, c j • x j ∈ maximalIdeal R := by
    refine sub_mem hy (sum_mem fun j _ => ?_)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hxm j)

  have hDz : ∀ i, Dfam i (y - ∑ j, c j • x j) = 0 := by
    intro i
    have hcf := (hD i).isCotangentFunctional
    have hsum : Dfam i (∑ j, c j • x j)
        = ∑ j, algebraMap 𝓞 (𝓴 𝓞) (c j) * Dfam i (x j) := by
      rw [show Dfam i (∑ j, c j • x j)
            = (AddMonoidHom.mk' (Dfam i) (hD i).map_add) (∑ j, c j • x j) from rfl, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show Dfam i (c j • x j) = _
      rw [Algebra.smul_def]
      exact hcf.map_algebraMap_mul (c j) (x j)
    rw [hcf.map_sub, hsum, hc i, sub_self]

  have hallz : ∀ D : R → 𝓴 𝓞, IsTangentVector R D → D (y - ∑ j, c j • x j) = 0 := by
    intro D hDt
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (hspan D hDt)
    · rintro _ ⟨i, rfl⟩
      exact hDz i
    · rfl
    · intro f g _ _ hf hg
      rw [Pi.add_apply, hf, hg, add_zero]
    · intro a f _ hf
      rw [Pi.smul_apply, hf, smul_zero]

  by_contra hzn
  obtain ⟨D, hDt, hDz'⟩ := exists_isTangentVector_apply_ne_zero le_sup_left hJ
    le_sup_right hzm hzn
  exact hDz' (hallz D hDt)

theorem exists_le_topologicalClosure_adjoin_range_eq_top
    (hD : ∀ i, IsTangentVector R (Dfam i))
    (hspan : ∀ D : R → 𝓴 𝓞, IsTangentVector R D →
      D ∈ Submodule.span (𝓴 𝓞) (Set.range Dfam)) :
    ∃ (n : ℕ) (x : Fin n → R), n ≤ d ∧ (∀ j, x j ∈ maximalIdeal R) ∧
      (Algebra.adjoin 𝓞 (Set.range x)).topologicalClosure = ⊤ := by
  obtain ⟨n, x, hnd, hxm, hx⟩ := exists_eval_eq_sum hD
  refine ⟨n, x, hnd, hxm, ?_⟩
  refine topologicalClosure_adjoin_range_eq_top_of_forall_isOpen x ?_
  intro y hy
  obtain ⟨c, hc⟩ := hx y hy
  exact ⟨c, fun J hJ _ => sub_sum_smul_mem_sup hD hspan hxm hy hc hJ⟩

end DualBasis

section QuantitativeGeneration

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
variable {R : ProartinianCat 𝓞}

lemma mem_span_range_val_of_isTangentVector {ι : Type*} (b : Module.Basis ι (𝓴 𝓞)
    (tangentSubmodule R)) {D : R → 𝓴 𝓞} (hD : IsTangentVector R D) :
    D ∈ Submodule.span (𝓴 𝓞) (Set.range fun i => ((b i : tangentSubmodule R) : R → 𝓴 𝓞)) := by
  have h1 : Set.range (fun i => ((b i : tangentSubmodule R) : R → 𝓴 𝓞))
      = (tangentSubmodule R).subtype '' Set.range b := by
    rw [← Set.range_comp]
    rfl
  rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  exact mem_tangentSubmodule.mpr hD

theorem exists_finrank_le_topologicalClosure_adjoin_range_eq_top
    [Module.Finite (𝓴 𝓞) (tangentSubmodule R)] :
    ∃ (n : ℕ) (x : Fin n → R), n ≤ Module.finrank (𝓴 𝓞) (tangentSubmodule R) ∧
      (∀ j, x j ∈ maximalIdeal R) ∧
      (Algebra.adjoin 𝓞 (Set.range x)).topologicalClosure = ⊤ := by
  classical
  set d := Module.finrank (𝓴 𝓞) (tangentSubmodule R) with hd
  let b : Module.Basis (Fin d) (𝓴 𝓞) (tangentSubmodule R) :=
    Module.finBasis (𝓴 𝓞) (tangentSubmodule R)
  have hD : ∀ i : Fin d, IsTangentVector R ((b i : tangentSubmodule R) : R → 𝓴 𝓞) := fun i =>
    mem_tangentSubmodule.mp (b i).2
  exact exists_le_topologicalClosure_adjoin_range_eq_top hD fun D hDt =>
    mem_span_range_val_of_isTangentVector b hDt

end QuantitativeGeneration

end ProartinianCat
end Deformation

namespace Deformation
p2m_export "Deformation" "ProartinianCat.tangentSubmodule ProartinianCat ProartinianCat.mvPowerSeriesObj"
p2m_open "Deformation"

open CategoryTheory IsLocalRing MvPowerSeries
open MvPowerSeries.WithPiTopology

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

namespace ProartinianCat
p2m_export "Deformation.ProartinianCat" "residueMap residueMap_add residueMap_algebraMap residueMap_eq_zero_of_mem isLocallyConstant_residueMap IsTangentVector tangentSubmodule mem_tangentSubmodule of Hom toResidueField algebra carrier mk hasEval_of_forall_mem_maximalIdeal mvPowerSeriesObj mvPowerSeriesObjX"
p2m_open "Deformation.ProartinianCat"

section Category

variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
variable [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]

variable {𝓞}

section Lift

variable {R : ProartinianCat 𝓞} {n : ℕ} (x : Fin n → R) (hx : ∀ j, x j ∈ maximalIdeal R)

noncomputable def mvPowerSeriesLift : mvPowerSeriesObj 𝓞 n ⟶ R := by
  letI := (maximalIdeal 𝓞).adicTopology
  letI : IsTopologicalRing 𝓞 := (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
  letI : IsAdicTopology 𝓞 := ⟨rfl⟩
  letI : UniformSpace 𝓞 := IsTopologicalAddGroup.rightUniformSpace 𝓞
  haveI : IsUniformAddGroup 𝓞 := isUniformAddGroup_of_addCommGroup
  letI : UniformSpace R.carrier := IsTopologicalAddGroup.rightUniformSpace R.carrier
  haveI : IsUniformAddGroup R.carrier := isUniformAddGroup_of_addCommGroup
  haveI : CompactSpace R.carrier := inferInstance
  haveI : T2Space R.carrier := inferInstance
  haveI : ContinuousSMul 𝓞 R.carrier :=
    continuousSMul_of_algebraMap _ _
      (isContinuous_of_isProartinian_of_isLocalHom (algebraMap 𝓞 R.carrier))
  exact ⟨ContinuousAlgHom.mk
    (MvPowerSeries.aeval (hasEval_of_forall_mem_maximalIdeal hx))
    (MvPowerSeries.continuous_aeval (hasEval_of_forall_mem_maximalIdeal hx))⟩

@[scoped simp]
theorem mvPowerSeriesLift_X (j : Fin n) :
    (mvPowerSeriesLift x hx).hom (mvPowerSeriesObjX j) = x j := by
  letI := (maximalIdeal 𝓞).adicTopology
  letI : IsTopologicalRing 𝓞 := (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
  letI : IsAdicTopology 𝓞 := ⟨rfl⟩
  letI : UniformSpace 𝓞 := IsTopologicalAddGroup.rightUniformSpace 𝓞
  haveI : IsUniformAddGroup 𝓞 := isUniformAddGroup_of_addCommGroup
  letI : UniformSpace R.carrier := IsTopologicalAddGroup.rightUniformSpace R.carrier
  haveI : IsUniformAddGroup R.carrier := isUniformAddGroup_of_addCommGroup
  haveI : CompactSpace R.carrier := inferInstance
  haveI : T2Space R.carrier := inferInstance
  haveI : ContinuousSMul 𝓞 R.carrier :=
    continuousSMul_of_algebraMap _ _
      (isContinuous_of_isProartinian_of_isLocalHom (algebraMap 𝓞 R.carrier))
  show MvPowerSeries.aeval (hasEval_of_forall_mem_maximalIdeal hx) (MvPowerSeries.X j) = x j
  rw [MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_X]

theorem surjective_mvPowerSeriesLift_of_dense
    (hgen : (Algebra.adjoin 𝓞 (Set.range x)).topologicalClosure = ⊤) :
    Function.Surjective (mvPowerSeriesLift x hx).hom := by

  set A : Subalgebra 𝓞 R.carrier := (mvPowerSeriesLift x hx).hom.toAlgHom.range with hA

  have hcompact : IsCompact (A : Set R.carrier) := by
    haveI : CompactSpace (mvPowerSeriesObj 𝓞 n).carrier := inferInstance
    exact isCompact_range (mvPowerSeriesLift x hx).hom.cont
  haveI : T2Space R.carrier := inferInstance
  have hclosed : IsClosed (A : Set R.carrier) := hcompact.isClosed

  have hsub : Algebra.adjoin 𝓞 (Set.range x) ≤ A := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact ⟨mvPowerSeriesObjX j, mvPowerSeriesLift_X x hx j⟩

  have htop : (⊤ : Subalgebra 𝓞 R.carrier) ≤ A := by
    rw [← hgen]
    exact Subalgebra.topologicalClosure_minimal hsub hclosed
  intro y
  exact htop (Algebra.mem_top (R := 𝓞) (A := R.carrier))

end Lift

theorem exists_surjective_mvPowerSeriesLift (R : ProartinianCat 𝓞)
    [Module.Finite (𝓴 𝓞) (tangentSubmodule R)] :
    ∃ (n : ℕ), n ≤ Module.finrank (𝓴 𝓞) (tangentSubmodule R) ∧
      ∃ f : mvPowerSeriesObj 𝓞 n ⟶ R, Function.Surjective f.hom := by
  obtain ⟨n, x, hn, hxm, hx⟩ :=
    exists_finrank_le_topologicalClosure_adjoin_range_eq_top (R := R)
  exact ⟨n, hn, mvPowerSeriesLift x hxm, surjective_mvPowerSeriesLift_of_dense x hxm hx⟩

end Category

end ProartinianCat
p2m_reactivate "P2MW.S_Deformation_ProartinianCat_exists_surjective_mvPowerSeriesLift.Deformation.ProartinianCat"
end Deformation
p2m_reactivate "P2MW.S_Deformation_ProartinianCat_exists_surjective_mvPowerSeriesLift.Deformation.ProartinianCat P2MW.S_Deformation_ProartinianCat_exists_surjective_mvPowerSeriesLift.Deformation"

theorem solution {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
    [IsNoetherianRing 𝓞] [Finite (IsLocalRing.ResidueField 𝓞)] [IsAdicComplete (IsLocalRing.maximalIdeal 𝓞) 𝓞]
    (R : Deformation.ProartinianCat 𝓞)
    [Module.Finite (IsLocalRing.ResidueField 𝓞) (Deformation.ProartinianCat.tangentSubmodule R)] :
    ∃ n : ℕ, n ≤ Module.finrank (IsLocalRing.ResidueField 𝓞) (Deformation.ProartinianCat.tangentSubmodule R) ∧
      ∃ f : Deformation.ProartinianCat.mvPowerSeriesObj 𝓞 n ⟶ R, Function.Surjective f.hom :=
  Deformation.ProartinianCat.exists_surjective_mvPowerSeriesLift R

end S_Deformation_ProartinianCat_exists_surjective_mvPowerSeriesLift
end P2MW
export P2MW.S_Deformation_ProartinianCat_exists_surjective_mvPowerSeriesLift (solution)
