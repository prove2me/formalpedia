-- Prove2me | solution 1 for Bl.general_b_fact_third_bis.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:10:32.506198+00:00
-- url     : https://prove2.me/submissions/9004daac-e57f-4027-bd74-00fd37cc64ad

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdBis_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_third_bis
namespace Bl.general_b_fact_third_bis
theorem _root_.solution :
  ∀ {E : Type u_1} [inst : Field.{u_1} E] [NumberField.{u_1} E] (φ : RingHom.{u_1, 0} E Complex) {n : Nat}
  (L : Submodule.{u_1, u_1} (NumberField.RingOfIntegers.{u_1} E) (Fin n → E)),
  Submodule.FG.{u_1, u_1} L →
    Eq.{u_1 + 1} (Submodule.span.{u_1, u_1} E (SetLike.coe.{u_1, u_1} L)) Top.top.{u_1} →
      ∀ (M : Matrix.{0, 0, u_1} (Fin n) (Fin n) E),
        (∀ (x : Fin n → E),
            Membership.mem.{u_1, u_1} L x → Membership.mem.{u_1, u_1} L (Matrix.mulVec.{u_1, 0, 0} M x)) →
          IsIntegral.{0, u_1} Int (Matrix.trace.{0, u_1} M) := by
  intro E _ _ φ n L hL hspan M hM
  classical
  have hKfg : (L.restrictScalars ℤ).FG := hL.restrictScalars
  have : Module.Finite ℤ (L.restrictScalars ℤ) := Module.Finite.iff_fg.mpr hKfg
  let g : (Fin n → E) →ₗ[ℤ] (Fin n → E) := (Matrix.mulVecLin M).restrictScalars ℤ
  have hg : ∀ x ∈ L.restrictScalars ℤ, g x ∈ L.restrictScalars ℤ := fun x hx => hM x hx
  let f : Module.End ℤ (L.restrictScalars ℤ) := g.restrict hg
  obtain ⟨p, hpm, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℤ f
  have hpow : ∀ (k : ℕ) (x : L.restrictScalars ℤ),
      (((f ^ k) x : L.restrictScalars ℤ) : Fin n → E) = (M ^ k).mulVec (x : Fin n → E) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec]
      rfl
  have hzL : ∀ x ∈ L, (Polynomial.aeval M p).mulVec x = 0 := by
    intro x hx
    have h := congrArg (fun h : Module.End ℤ (L.restrictScalars ℤ) =>
      ((h ⟨x, hx⟩ : L.restrictScalars ℤ) : Fin n → E)) hp0
    simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, hpow, LinearMap.zero_apply,
      Submodule.coe_zero] at h
    rw [Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec]
    simpa only [Matrix.smul_mulVec] using h
  have hz : Polynomial.aeval M p = 0 := by
    have hlin : Matrix.mulVecLin (Polynomial.aeval M p) = 0 :=
      LinearMap.ext_on hspan (fun x hx => by simpa using hzL x hx)
    ext i j
    have := congrFun (LinearMap.congr_fun hlin (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one] using this
  have hN : Polynomial.aeval (M.map φ) p = 0 := by
    have h2 := congrArg (φ.mapMatrix (m := Fin n)) hz
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂] at h2
    rw [Polynomial.aeval_def]
    convert h2 using 2 <;> first | exact RingHom.ext_int _ _ | rfl
  have htr : (M.map φ).trace = φ M.trace := by
    simp [Matrix.trace, map_sum]
  have hint : IsIntegral ℤ (φ M.trace) := by
    rw [← htr, Matrix.trace_eq_sum_roots_charpoly]
    refine IsIntegral.multiset_sum fun r hr => ?_
    have hroot := (Polynomial.mem_roots'.mp hr).2
    have hsp := Matrix.mem_spectrum_of_isRoot_charpoly hroot
    refine ⟨p, hpm, ?_⟩
    have h1 := spectrum.subset_polynomial_aeval (M.map φ) (p.map (algebraMap ℤ ℂ)) ⟨r, hsp, rfl⟩
    rw [Polynomial.aeval_map_algebraMap, hN] at h1
    rcases subsingleton_or_nontrivial (Matrix (Fin n) (Fin n) ℂ) with hs | hs
    · exact absurd hsp (by rw [spectrum.mem_iff, not_not]; exact isUnit_of_subsingleton _)
    · rw [spectrum.zero_eq, Set.mem_singleton_iff] at h1
      simpa [Polynomial.eval_map, Polynomial.aeval_def] using h1
  exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).mp hint
end Bl.general_b_fact_third_bis
