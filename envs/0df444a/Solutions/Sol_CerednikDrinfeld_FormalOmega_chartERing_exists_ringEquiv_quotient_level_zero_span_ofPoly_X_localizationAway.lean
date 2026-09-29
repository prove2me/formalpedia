-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.chartERing.exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8ae4b43e-a3f1-5922-8dac-dd7924b09bce

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace BranchIso29

variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ)

theorem algebraMap_pi_eq_zero (T : Type) [CommRing T] [Algebra 𝒪 T] [Algebra (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) T] [IsScalarTower 𝒪 (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) T] :
    algebraMap 𝒪 T π = 0 := by
  rw [IsScalarTower.algebraMap_apply 𝒪 (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) T, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), map_zero]

noncomputable def pt (hr : 1 < r) (i : Fin 2) : (chartE 𝒪 π r).obj (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) :=
  ⟨(if i = 0 then 0 else algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.X ()),
    if i = 0 then algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.X ()) else 0), by
    have hπ0 : algebraMap 𝒪 (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) π = 0 := algebraMap_pi_eq_zero 𝒪 π (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1))
    have hu0 : IsUnit ((0 : (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1))) ^ (r - 1) - 1) := by
      rw [zero_pow (by omega), zero_sub]; exact isUnit_one.neg
    have hut : IsUnit ((algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.X ())) ^ (r - 1) - 1) := by
      rw [← map_pow, ← map_one (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1))), ← map_sub]
      exact IsLocalization.Away.algebraMap_isUnit _
    refine ⟨?_, ?_, ?_⟩
    · split_ifs <;> simp [hπ0]
    · split_ifs <;> assumption
    · split_ifs <;> assumption⟩

theorem evalPoly_pt_X_self (hr : 1 < r) (i : Fin 2) :
    chartERing.evalPoly (pt 𝒪 π r hr i) (MvPolynomial.X i) = 0 := by
  fin_cases i <;> simp [chartERing.evalPoly, pt, MvPolynomial.aeval_X]

theorem evalPoly_pt_X_other (hr : 1 < r) (i : Fin 2) :
    chartERing.evalPoly (pt 𝒪 π r hr i) (MvPolynomial.X (1 - i)) =
      algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.X ()) := by
  fin_cases i <;> simp [chartERing.evalPoly, pt, MvPolynomial.aeval_X]

noncomputable def F₀ (hr : 1 < r) (i : Fin 2) : chartERing 𝒪 π r →ₐ[𝒪] (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) := chartERing.lift (pt 𝒪 π r hr i)

noncomputable def F₁ (hr : 1 < r) (i : Fin 2) : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) →ₐ[𝒪] (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) :=
  Ideal.Quotient.liftₐ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (F₀ 𝒪 π r hr i) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_pow, AlgHom.commutes, algebraMap_pi_eq_zero 𝒪 π (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)), zero_pow (by omega), mul_zero])

theorem F₁_mk (hr : 1 < r) (i : Fin 2) (x : chartERing 𝒪 π r) :
    F₁ 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) x) = F₀ 𝒪 π r hr i x := rfl

noncomputable def F (hr : 1 < r) (i : Fin 2) : (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})) →ₐ[𝒪] (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) :=
  Ideal.Quotient.liftₐ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (F₁ 𝒪 π r hr i) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, F₁_mk, F₀, chartERing.lift_ofPoly, evalPoly_pt_X_self, mul_zero])

theorem F_mk_mk (hr : 1 < r) (i : Fin 2) (x : chartERing 𝒪 π r) :
    F 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) x)) = chartERing.lift (pt 𝒪 π r hr i) x := rfl

theorem F_algebraMap (hr : 1 < r) (i : Fin 2) (a : 𝒪) :
    F 𝒪 π r hr i (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a))) =
      algebraMap (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) _ (Ideal.Quotient.mk _ a) := by
  rw [F_mk_mk, AlgHom.commutes, IsScalarTower.algebraMap_apply 𝒪 (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)), Ideal.Quotient.algebraMap_eq]

theorem F_X_other (hr : 1 < r) (i : Fin 2) :
    F 𝒪 π r hr i (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) =
      algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ()) := by
  rw [F_mk_mk, chartERing.lift_ofPoly, evalPoly_pt_X_other]

theorem F_X_self (hr : 1 < r) (i : Fin 2) :
    F 𝒪 π r hr i (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i)))) = 0 := by
  rw [F_mk_mk, chartERing.lift_ofPoly, evalPoly_pt_X_self]

theorem algebraMap_C (c : (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) :
    algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.C c) = algebraMap (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) c := by
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

theorem F_comp_G (hr : 1 < r) (i : Fin 2) (G : (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) →+* (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})))
    (hGC : ∀ a : 𝒪, G (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.C (Ideal.Quotient.mk _ a))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a)))
    (hGX : G (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ())) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) :
    (F 𝒪 π r hr i).toRingHom.comp G = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1))
  apply MvPolynomial.ringHom_ext
  · intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.id_comp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hGC,
      F_algebraMap, algebraMap_C]
  · intro u
    cases u
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.id_comp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hGX, F_X_other]

theorem fin2_cases (i j : Fin 2) : j = i ∨ j = 1 - i := by
  fin_cases i <;> fin_cases j <;> decide

theorem ofPoly_eq (p : MvPolynomial (Fin 2) 𝒪) :
    chartERing.ofPoly 𝒪 π r p = algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r) (Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π}) p) := rfl

theorem F_X_self' (hr : 1 < r) (i : Fin 2) :
    F 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.X i))))) = 0 :=
  F_X_self 𝒪 π r hr i

theorem F_X_other' (hr : 1 < r) (i : Fin 2) :
    F 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.X (1 - i)))))) =
      algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ()) :=
  F_X_other 𝒪 π r hr i

theorem mk_mk_X_self (i : Fin 2) :
    Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.X i)))) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

theorem F_algebraMap' (hr : 1 < r) (i : Fin 2) (a : 𝒪) :
    F 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.C a))))) =
      algebraMap (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) _ (Ideal.Quotient.mk _ a) := by
  have h1 : (algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.C a)) = algebraMap 𝒪 (chartERing 𝒪 π r) a := by
    rw [← ofPoly_eq, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rw [h1]; exact F_algebraMap 𝒪 π r hr i a

theorem mk_mk_C (i : Fin 2) (a : 𝒪) :
    Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.C a)))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a)) := by
  have h1 : (algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.C a)) = algebraMap 𝒪 (chartERing 𝒪 π r) a := by
    rw [← ofPoly_eq, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rw [h1]

theorem G_comp_F (hr : 1 < r) (i : Fin 2) (G : (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) →+* (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})))
    (hGC : ∀ a : 𝒪, G (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.C (Ideal.Quotient.mk _ a))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a)))
    (hGX : G (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ())) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) :
    G.comp (F 𝒪 π r hr i).toRingHom = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (edgeQuot.discr 𝒪 π r))
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_))
  · show G (F 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.C a)))))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.C a))))
    exact ((congrArg G (F_algebraMap' 𝒪 π r hr i a)).trans ((congrArg G (algebraMap_C 𝒪 π r _).symm).trans (hGC a))).trans
      (mk_mk_C 𝒪 π r i a).symm
  · show G (F 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.X j)))))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.X j))))
    rcases fin2_cases i j with hj | hj
    · subst hj
      exact ((congrArg G (F_X_self' 𝒪 π r hr j)).trans (map_zero G)).trans (mk_mk_X_self 𝒪 π r j).symm
    · subst hj
      exact (congrArg G (F_X_other' 𝒪 π r hr i)).trans hGX

theorem assemble (hr : 1 < r) (i : Fin 2) (G : (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) →+* (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})))
    (hGC : ∀ a : 𝒪, G (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.C (Ideal.Quotient.mk _ a))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a)))
    (hGX : G (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ())) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) :
    ∃ e : (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})) ≃+* (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)),
      (∀ a : 𝒪, e (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a))) =
          algebraMap (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) _ (Ideal.Quotient.mk _ a)) ∧
      e (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) =
          algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ()) :=
  ⟨RingEquiv.ofRingHom (F 𝒪 π r hr i).toRingHom G (F_comp_G 𝒪 π r hr i G hGC hGX) (G_comp_F 𝒪 π r hr i G hGC hGX),
    fun a => F_algebraMap 𝒪 π r hr i a, F_X_other 𝒪 π r hr i⟩

end BranchIso29

namespace BranchIso29G

section

variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (i : Fin 2)

theorem isUnit_ofPoly_X_pow_sub_one (j : Fin 2) :
    IsUnit ((chartERing.ofPoly 𝒪 π r (MvPolynomial.X j)) ^ (r - 1) - 1) := by
  fin_cases j
  · exact isUnit_of_mul_isUnit_left (chartERing.isUnit_discr 𝒪 π r)
  · exact isUnit_of_mul_isUnit_right (chartERing.isUnit_discr 𝒪 π r)

noncomputable def cG : (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) →+* (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})) :=
  Ideal.Quotient.lift (Ideal.span {π ^ (0 + 1)})
    ((Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})).comp ((Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})).comp (algebraMap 𝒪 (chartERing 𝒪 π r))))
    (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      have h : algebraMap 𝒪 (chartERing 𝒪 π r) (b * π ^ (0 + 1)) ∈ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) := by
        rw [map_mul (algebraMap 𝒪 (chartERing 𝒪 π r)), map_pow (algebraMap 𝒪 (chartERing 𝒪 π r))]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero])

theorem cG_mk (a : 𝒪) :
    cG 𝒪 π r i (Ideal.Quotient.mk (Ideal.span {π ^ (0 + 1)}) a) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a)) :=
  rfl

noncomputable def gG : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) →+* (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})) :=
  MvPolynomial.eval₂Hom (cG 𝒪 π r i)
    (fun _ => Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i)))))

theorem gG_X : gG 𝒪 π r i (MvPolynomial.X ()) =
    Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i)))) := by
  rw [gG, MvPolynomial.eval₂Hom_X']

theorem gG_C (a : 𝒪) : gG 𝒪 π r i (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {π ^ (0 + 1)}) a)) =
    Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a)) := by
  rw [gG, MvPolynomial.eval₂Hom_C]; rfl

set_option synthInstance.maxHeartbeats 1600000 in
theorem isUnit_gG : IsUnit (gG 𝒪 π r i ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) := by
  have h : gG 𝒪 π r i ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1) =
      (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) ^ (r - 1) - 1 := by
    rw [map_sub (gG 𝒪 π r i), map_pow (gG 𝒪 π r i), map_one (gG 𝒪 π r i), gG_X]
  have hu := (isUnit_ofPoly_X_pow_sub_one 𝒪 π r (1 - i)).map
    ((Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})).comp (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})))
  rw [map_sub ((Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})).comp (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))),
    map_pow ((Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})).comp (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))),
    map_one ((Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})).comp (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))), RingHom.comp_apply] at hu
  rw [h]
  exact hu

noncomputable def G : (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) →+* (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})) :=
  IsLocalization.Away.lift ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1) (isUnit_gG 𝒪 π r i)

theorem G_algebraMap (p : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) :
    G 𝒪 π r i (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) p) = gG 𝒪 π r i p :=
  IsLocalization.Away.lift_eq _ (isUnit_gG 𝒪 π r i) p

theorem G_algebraMap_C (a : 𝒪) :
    G 𝒪 π r i (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {π ^ (0 + 1)}) a))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a)) := by
  rw [G_algebraMap, gG_C]

theorem G_algebraMap_X :
    G 𝒪 π r i (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.X ())) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i)))) := by
  rw [G_algebraMap, gG_X]

end

end BranchIso29G

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (hπ : (Ideal.span ({π} : Set 𝒪)).IsMaximal) (hr : 1 < r) (i : Fin 2) :
    ∃ e : (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) ≃+*
        Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1),
      (∀ a : 𝒪, e (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a))) =
          algebraMap (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) _ (Ideal.Quotient.mk _ a)) ∧
      e (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) =
          algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ()) := by
  obtain ⟨e, he₁, he₂⟩ := BranchIso29.assemble 𝒪 π r hr i (BranchIso29G.G 𝒪 π r i)
    (BranchIso29G.G_algebraMap_C 𝒪 π r i) (BranchIso29G.G_algebraMap_X 𝒪 π r i)
  exact ⟨e, he₁, he₂⟩

end S_CerednikDrinfeld_FormalOmega_chartERing_exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway (solution)
