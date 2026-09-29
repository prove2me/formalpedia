-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isAtkinLehnerQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/96b40827-64e0-531c-9269-4d9523286a66

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isAtkinLehnerQuotient
p2m_attr_erase "instance" "CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction"
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve QuaternionAlgebra
open scoped Quaternion

universe u

namespace ALQExists

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

section Conj

variable (π : ℍ[ℚ, a, b]) (hu : IsUnit π) (hnorm : ∀ x ∈ Λ, ∃ y ∈ Λ, π * x = y * π)

noncomputable def conj (x : ↥Λ) : ↥Λ :=
  ⟨(hnorm x x.2).choose, (hnorm x x.2).choose_spec.1⟩

theorem conj_spec (x : ↥Λ) : π * (x : ℍ[ℚ, a, b]) = (conj π hnorm x : ℍ[ℚ, a, b]) * π :=
  (hnorm x x.2).choose_spec.2

include hu in
theorem conj_unique {x : ↥Λ} {y : ℍ[ℚ, a, b]} (h : π * (x : ℍ[ℚ, a, b]) = y * π) :
    (conj π hnorm x : ℍ[ℚ, a, b]) = y :=
  (hu.mul_left_inj).1 ((conj_spec π hnorm x).symm.trans h)

include hu in
theorem conj_one (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) : conj π hnorm ⟨1, h1⟩ = ⟨1, h1⟩ :=
  Subtype.ext (conj_unique π hu hnorm (by rw [mul_one, one_mul]))

include hu in
theorem conj_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    (conj π hnorm ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ : ℍ[ℚ, a, b]) =
      (conj π hnorm x : ℍ[ℚ, a, b]) * (conj π hnorm y : ℍ[ℚ, a, b]) :=
  conj_unique π hu hnorm (by
    show π * ((x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b])) = _
    rw [← mul_assoc, conj_spec π hnorm x, mul_assoc, conj_spec π hnorm y, mul_assoc])

include hu in
theorem conj_add (x y : ↥Λ) : conj π hnorm (x + y) = conj π hnorm x + conj π hnorm y :=
  Subtype.ext (conj_unique π hu hnorm (by
    show π * ((x : ℍ[ℚ, a, b]) + (y : ℍ[ℚ, a, b])) = ((conj π hnorm x : ℍ[ℚ, a, b]) + (conj π hnorm y : ℍ[ℚ, a, b])) * π
    rw [mul_add, add_mul, conj_spec π hnorm x, conj_spec π hnorm y]))

include hu in

theorem conj_coe (c : ℚ) (hc : ((c : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    (conj π hnorm ⟨(c : ℍ[ℚ, a, b]), hc⟩ : ℍ[ℚ, a, b]) = (c : ℍ[ℚ, a, b]) :=
  conj_unique π hu hnorm (by rw [coe_commutes])

include hu in

theorem conj_add_star (m : ↥Λ) (n : ℤ) (hn : (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]))
    (hν : nrd π ≠ 0) :
    (conj π hnorm m : ℍ[ℚ, a, b]) + star (conj π hnorm m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) := by
  set c : ℍ[ℚ, a, b] := (conj π hnorm m : ℍ[ℚ, a, b]) with hc
  have h1 : π * (m : ℍ[ℚ, a, b]) = c * π := conj_spec π hnorm m

  have h2 : star (m : ℍ[ℚ, a, b]) * star π = star π * star c := by
    rw [← star_mul, ← star_mul, h1]
  have h3 : π * star (m : ℍ[ℚ, a, b]) = star c * π := by
    have e1 : π * (star (m : ℍ[ℚ, a, b]) * star π) * π = π * (star π * star c) * π := by rw [h2]
    have e2 : π * star (m : ℍ[ℚ, a, b]) * ((nrd π : ℚ) : ℍ[ℚ, a, b]) = ((nrd π : ℚ) : ℍ[ℚ, a, b]) * (star c * π) := by
      rw [← star_mul_eq_coe_nrd π]
      calc π * star (m : ℍ[ℚ, a, b]) * (star π * π) = π * (star (m : ℍ[ℚ, a, b]) * star π) * π := by simp only [mul_assoc]
        _ = π * (star π * star c) * π := e1
        _ = (π * star π) * (star c * π) := by simp only [mul_assoc]
        _ = (star π * π) * (star c * π) := by rw [mul_star_eq_coe_nrd, star_mul_eq_coe_nrd]
    rw [← coe_commutes] at e2
    rw [coe_mul_eq_smul, coe_mul_eq_smul] at e2
    exact smul_right_injective ℍ[ℚ, a, b] hν e2
  have h4 : (c + star c) * π = ((n : ℚ) : ℍ[ℚ, a, b]) * π := by
    rw [add_mul, ← h1, ← h3, ← mul_add, hn, coe_commutes]
  exact (hu.mul_left_inj).1 h4

end Conj

theorem pushPt_congr {N : ℕ} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) {m m' : ↥Λ} (h : m = m')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f) :
    pushPt (E.act m) (E.act_over m) P = pushPt (E.act m') (E.act_over m') P := by
  subst h; rfl

noncomputable def twist {N : ℕ} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S)
    (π : ℍ[ℚ, a, b]) (hu : IsUnit π) (hν : nrd π ≠ 0)
    (hnorm : ∀ x ∈ Λ, ∃ y ∈ Λ, π * x = y * π) : FakeEllipticCurve Λ N S where
  A := E.A
  f := E.f
  L := E.L
  comm := E.comm
  bundle := E.bundle
  dim_fibre := E.dim_fibre
  act x := E.act (conj π hnorm x)
  act_over x := E.act_over _
  act_hom x := E.act_hom _
  act_one h := by
    show E.act (conj π hnorm ⟨1, h⟩) = 𝟙 E.A
    rw [conj_one π hu hnorm h]; exact E.act_one h
  act_mul x y h := by
    show E.act (conj π hnorm ⟨_, h⟩) = E.act (conj π hnorm y) ≫ E.act (conj π hnorm x)
    have hm : ((conj π hnorm x : ℍ[ℚ, a, b]) * (conj π hnorm y : ℍ[ℚ, a, b])) ∈ Λ := by
      rw [← conj_mul π hu hnorm x y h]; exact (conj π hnorm _).2
    rw [← E.act_mul (conj π hnorm x) (conj π hnorm y) hm]
    congr 1; exact Subtype.ext (conj_mul π hu hnorm x y h)
  act_add x y := by
    intro T t P
    show pushPt (E.act (conj π hnorm (x + y))) (E.act_over _) P =
      E.L.mul t (pushPt (E.act (conj π hnorm x)) (E.act_over _) P) (pushPt (E.act (conj π hnorm y)) (E.act_over _) P)
    rw [pushPt_congr E (conj_add π hu hnorm x y)]
    exact E.act_add _ _ t P
  act_trace := by
    intro k _ _ sk V _ _ _ τ hτ hrange hadd hscale m Φ hΦ n hn
    exact E.act_trace k sk V τ hτ hrange hadd hscale (conj π hnorm m) Φ hΦ n (conj_add_star π hu hnorm m n hn hν)
  C := E.C
  lev := E.lev
  lev_closed := E.lev_closed
  lev_sub := E.lev_sub
  lev_one := E.lev_one
  lev_torsion := E.lev_torsion
  lev_stable x := E.lev_stable _
  lev_finite := E.lev_finite
  lev_flat := E.lev_flat
  lev_finitePresentation := E.lev_finitePresentation
  lev_rank := E.lev_rank
  lev_fibre := E.lev_fibre

noncomputable def twistT {N ℓ : ℕ} {S : Type u} [CommRing S] (u : WithExtraLevel Λ N ℓ S)
    (π : ℍ[ℚ, a, b]) (hu : IsUnit π) (hν : nrd π ≠ 0)
    (hnorm : ∀ x ∈ Λ, ∃ y ∈ Λ, π * x = y * π) : WithExtraLevel Λ N ℓ S :=
  ⟨twist u.1 π hu hν hnorm,
   { K := u.2.K
     levK := u.2.levK
     levK_closed := u.2.levK_closed
     levK_sub := u.2.levK_sub
     levK_one := u.2.levK_one
     levK_torsion := u.2.levK_torsion
     levK_stable := fun x => u.2.levK_stable _
     levK_disjoint := u.2.levK_disjoint
     levK_finite := u.2.levK_finite
     levK_flat := u.2.levK_flat
     levK_finitePresentation := u.2.levK_finitePresentation
     levK_rank := u.2.levK_rank
     levK_fibre := u.2.levK_fibre }⟩

end ALQExists

open ALQExists in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q') (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (S : Type) [CommRing S] (u : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    ∃ u' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S, QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u u' := by
  classical
  set E : QM.FakeEllipticCurve Λ N S := u.1 with hEu
  have hO : IsOrder Λ := hΛ.isOrder
  obtain ⟨π, hπΛ, hnrd, hnormL, hnormR, hgen⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ r hr
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hrp.ne_zero
  have hν : nrd π ≠ 0 := by rcases hnrd with h | h <;> rw [h] <;> simp [hr0]
  have hπ0 : π ≠ 0 := by rintro rfl; exact hν (by simp)
  have hu : IsUnit π := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB π hπ0

  obtain ⟨s, hs1, hsν⟩ : ∃ s : ℚ, (s = 1 ∨ s = -1) ∧ s * nrd π = r := by
    rcases hnrd with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; ring⟩
  have hπbar : star π ∈ Λ := by
    obtain ⟨-, t, ht⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hπΛ
    have : star π = ((trd π : ℚ) : ℍ[ℚ, a, b]) - π := by rw [← add_star_eq_coe_trd]; abel
    rw [this, ← ht]
    refine Λ.sub_mem ?_ hπΛ
    have : (((t : ℚ)) : ℍ[ℚ, a, b]) = (t : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one]; norm_cast
    rw [this]; exact Λ.smul_mem _ hO.one_mem
  set πd : ℍ[ℚ, a, b] := (s : ℍ[ℚ, a, b]) * star π with hπd
  have hπdΛ : πd ∈ Λ := by
    rcases hs1 with rfl | rfl
    · simpa [hπd] using hπbar
    · have : πd = -star π := by simp [hπd]
      rw [this]; exact Λ.neg_mem hπbar
  have hππd : π * πd = ((r : ℚ) : ℍ[ℚ, a, b]) := by
    rw [hπd, ← mul_assoc, ← coe_commutes s π, mul_assoc, mul_star_eq_coe_nrd, ← coe_mul, hsν]
  have hπdπ : πd * π = ((r : ℚ) : ℍ[ℚ, a, b]) := by
    rw [hπd, mul_assoc, star_mul_eq_coe_nrd, ← coe_mul, hsν]
  refine ⟨twistT u π hu hν hnormL, ?_⟩
  refine ⟨E.act ⟨π, hπΛ⟩, E.act_over _, E.act ⟨πd, hπdΛ⟩, E.act_over _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T t P Q; exact E.act_hom _ t P Q
  · intro T t P Q; exact E.act_hom _ t P Q
  ·
    intro x
    show E.act x ≫ E.act ⟨π, hπΛ⟩ = E.act ⟨π, hπΛ⟩ ≫ E.act (conj π hnormL x)
    have h1 : π * (x : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem hπΛ x.2
    have h2 : (conj π hnormL x : ℍ[ℚ, a, b]) * π ∈ Λ := hO.mul_mem (conj π hnormL x).2 hπΛ
    rw [← E.act_mul ⟨π, hπΛ⟩ x h1, ← E.act_mul (conj π hnormL x) ⟨π, hπΛ⟩ h2]
    congr 1; exact Subtype.ext (conj_spec π hnormL x)
  ·
    intro x
    show E.act (conj π hnormL x) ≫ E.act ⟨πd, hπdΛ⟩ = E.act ⟨πd, hπdΛ⟩ ≫ E.act x
    have h1 : πd * (conj π hnormL x : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem hπdΛ (conj π hnormL x).2
    have h2 : (x : ℍ[ℚ, a, b]) * πd ∈ Λ := hO.mul_mem x.2 hπdΛ
    rw [← E.act_mul ⟨πd, hπdΛ⟩ (conj π hnormL x) h1, ← E.act_mul x ⟨πd, hπdΛ⟩ h2]
    congr 1; apply Subtype.ext
    show πd * (conj π hnormL x : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) * πd

    have e : πd * (π * (x : ℍ[ℚ, a, b])) * πd = πd * ((conj π hnormL x : ℍ[ℚ, a, b]) * π) * πd := by
      rw [conj_spec π hnormL x]
    have e' : ((r : ℚ) : ℍ[ℚ, a, b]) * ((x : ℍ[ℚ, a, b]) * πd) = ((r : ℚ) : ℍ[ℚ, a, b]) * (πd * (conj π hnormL x : ℍ[ℚ, a, b])) := by
      calc ((r : ℚ) : ℍ[ℚ, a, b]) * ((x : ℍ[ℚ, a, b]) * πd) = (πd * π) * (x : ℍ[ℚ, a, b]) * πd := by rw [hπdπ]; simp only [mul_assoc]
        _ = πd * (π * (x : ℍ[ℚ, a, b])) * πd := by simp only [mul_assoc]
        _ = πd * ((conj π hnormL x : ℍ[ℚ, a, b]) * π) * πd := e
        _ = πd * (conj π hnormL x : ℍ[ℚ, a, b]) * (π * πd) := by simp only [mul_assoc]
        _ = ((r : ℚ) : ℍ[ℚ, a, b]) * (πd * (conj π hnormL x : ℍ[ℚ, a, b])) := by rw [hππd, ← coe_commutes]
    rw [coe_mul_eq_smul, coe_mul_eq_smul] at e'
    exact (smul_right_injective ℍ[ℚ, a, b] hr0 e').symm
  ·
    intro hrΛ
    constructor
    · have hm := E.act_mul ⟨πd, hπdΛ⟩ ⟨π, hπΛ⟩ (hO.mul_mem hπdΛ hπΛ)
      refine hm.symm.trans ?_
      congr 1; exact Subtype.ext hπdπ
    · show E.act ⟨πd, hπdΛ⟩ ≫ E.act ⟨π, hπΛ⟩ = E.act (conj π hnormL ⟨_, hrΛ⟩)
      rw [← E.act_mul ⟨π, hπΛ⟩ ⟨πd, hπdΛ⟩ (hO.mul_mem hπΛ hπdΛ)]
      congr 1; apply Subtype.ext
      rw [conj_coe π hu hnormL (r : ℚ) hrΛ]; exact hππd
  ·
    intro T t P
    constructor
    · intro hP m n hmn

      have hdiv : ∃ n' : ℤ, nrd (m : ℍ[ℚ, a, b]) = (r : ℚ) * n' := by
        refine ⟨n, ?_⟩
        have h := hmn
        rw [mul_star_eq_coe_nrd] at h
        have h' := QuaternionAlgebra.coe_injective h
        exact_mod_cast h'
      obtain ⟨l, hl, hml⟩ := (hgen m m.2).1 hdiv
      have hlπ : (l : ℍ[ℚ, a, b]) * π ∈ Λ := hO.mul_mem hl hπΛ
      have hmeq : m = ⟨(l : ℍ[ℚ, a, b]) * π, hlπ⟩ := Subtype.ext hml
      rw [pushPt_congr E hmeq]
      have hsplit : pushPt (E.act ⟨(l : ℍ[ℚ, a, b]) * π, hlπ⟩) (E.act_over _) P =
          mapPt (E.act ⟨l, hl⟩) (E.act_over _) (mapPt (E.act ⟨π, hπΛ⟩) (E.act_over _) P) := by
        apply Subtype.ext
        simp only [pushPt, mapPt_coe, Category.assoc, E.act_mul ⟨l, hl⟩ ⟨π, hπΛ⟩ hlπ]
      rw [hsplit, show mapPt (E.act ⟨π, hπΛ⟩) (E.act_over _) P = E.L.one t from hP]

      set x := mapPt (E.act ⟨l, hl⟩) (E.act_over _) (E.L.one t) with hx
      have hxx : E.L.mul t x x = x := by rw [hx, ← E.act_hom, E.L.one_mul]
      letI := E.L.pointGroup t
      have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
      exact mul_left_cancel h2
    · intro hK

      have hss : s * s = 1 := by rcases hs1 with rfl | rfl <;> norm_num
      have hnrds : nrd π = (r : ℚ) * s := by
        calc nrd π = s * (s * nrd π) := by rw [← mul_assoc, hss, one_mul]
          _ = (r : ℚ) * s := by rw [hsν, mul_comm]
      obtain ⟨z, hz⟩ : ∃ z : ℤ, (z : ℚ) = s := by
        rcases hs1 with rfl | rfl
        · exact ⟨1, by simp⟩
        · exact ⟨-1, by simp⟩
      have hnπ : π * star π = (((r : ℤ) * z : ℚ) : ℍ[ℚ, a, b]) := by
        rw [mul_star_eq_coe_nrd, hnrds, ← hz]; norm_cast
      exact hK ⟨π, hπΛ⟩ z hnπ
  · intro T t P hP
    exact E.lev_stable _ t P hP
  · intro T t P hP
    exact u.2.levK_stable _ t P hP

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isAtkinLehnerQuotient
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isAtkinLehnerQuotient (solution)
