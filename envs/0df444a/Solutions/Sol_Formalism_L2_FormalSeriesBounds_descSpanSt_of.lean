-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.descSpanSt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:20:34.077072+00:00
-- url     : https://prove2.me/submissions/e14a4609-bab3-4032-b102-5cb61bfa85c1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_nab_eq_nabL
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_const_dpolyN_lin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_exists_fin_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_nabL_trunc
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (hS : HaSpanSt) : DescSpanSt Xo c := by
  intro T io y C3 C _ _ V ι _hι k Y _hY a n P hP f hf
  have : CharZero T.Fr := charZero_of_inj_zero fun x hx => by
    have h1 := congrArg ι hx
    rwa [map_natCast, map_zero, Nat.cast_eq_zero] at h1
  obtain ⟨m, cc, Z, hc, hZ, hPe⟩ :=
    hS (E →+* ℂ) Dw.mult n ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) C V.RR P hP
  let Q : Fin m → MvPolynomial (LtN Dw n) T.Fr := fun i => MvPolynomial.map (Int.castRingHom T.Fr) (Z i)
  have hmap : ∀ i, MvPolynomial.map ι (Q i) = MvPolynomial.map (Int.castRingHom C) (Z i) := by
    intro i
    simp only [Q]
    rw [MvPolynomial.map_map, RingHom.ext_int (ι.comp (Int.castRingHom T.Fr)) (Int.castRingHom C)]
  let Ls := chartLetterSystem C3 V ι a
  let tc : (Fin n × Fin (chD C3.ch) →₀ ℕ) → C := fun μ =>
    MvPolynomial.coeff μ (MvPowerSeries.trunc' C (DescP.cst P.totalDegree) f)
  have hP2 : ∀ g : PS C n (chD C3.ch),
      Y.nab Ls n g P = ∑ i, cc i * Y.nab Ls n g (MvPolynomial.map ι (Q i)) := by
    intro g
    have hg : ∀ i, Y.nab Ls n g (MvPolynomial.map ι (Q i)) = Y.nab Ls n g (MvPolynomial.map (Int.castRingHom C) (Z i)) :=
      fun i => congrArg (Y.nab Ls n g) (hmap i)
    simp only [hg, nab_eq_nabL]
    show MvPowerSeries.constantCoeff (DpolyN (Y.B.FK C) (Ls.cp n) (Ls.uv n) P (g * gofY Y n)) =
      ∑ i, cc i * MvPowerSeries.constantCoeff
        (DpolyN (Y.B.FK C) (Ls.cp n) (Ls.uv n) (MvPolynomial.map (Int.castRingHom C) (Z i)) (g * gofY Y n))
    rw [hPe]
    exact DescP.const_dpolyN_lin (Y.B.FK C) (Ls.cp n) (Ls.uv n) Finset.univ cc _ (g * gofY Y n)
  have hmono : ∀ μ : Fin n × Fin (chD C3.ch) →₀ ℕ,
      (MvPowerSeries.monomial μ (1 : C) : PS C n (chD C3.ch)) =
        MvPowerSeries.map ι (MvPowerSeries.monomial μ (1 : T.Fr)) := by
    intro μ
    rw [MvPowerSeries.map_monomial, ι.map_one]
  let S := (MvPowerSeries.trunc' C (DescP.cst P.totalDegree) f).support
  let g' : (Fin n × Fin (chD C3.ch) →₀ ℕ) × Fin m → C := fun x =>
    (tc x.1 * cc x.2) * Y.nab Ls n (MvPowerSeries.map ι (MvPowerSeries.monomial x.1 (1 : T.Fr)))
      (MvPolynomial.map ι (Q x.2))
  have hmain : Y.nab Ls n f P = ∑ x ∈ S ×ˢ (Finset.univ : Finset (Fin m)), g' x := by
    rw [Finset.sum_product, nab_eq_nabL, DescP.nabL_trunc]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← nab_eq_nabL, hP2, hmono μ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g', tc]
    ring
  obtain ⟨N, e, _he, hsum⟩ := DescP.exists_fin_sum (S ×ˢ (Finset.univ : Finset (Fin m))) g'
  refine ⟨N, fun j => tc (e j).1 * cc (e j).2, fun j => Q (e j).2,
    fun j => MvPowerSeries.monomial (e j).1 (1 : T.Fr), ?_, ?_, ?_, ?_⟩
  · intro j
    have htc : V.Ge 0 (tc (e j).1) := by
      simp only [tc]
      rw [MvPowerSeries.coeff_trunc']
      split_ifs
      · exact hf _
      · exact VF.Ge.zero 0
    exact VF.Ge.mul_int htc (hc (e j).2)
  · intro j
    refine ⟨hZ (e j).2 T.Fr, fun μ => ?_⟩
    simp only [Q]
    rw [MvPolynomial.coeff_map, eq_intCast]
    exact ⟨((MvPolynomial.coeff μ (Z (e j).2) : ℤ) : T.V), map_intCast _ _⟩
  · intro j μ
    rw [MvPowerSeries.coeff_monomial]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · rw [hmain, hsum]
end Formalism.L2.FormalSeriesBounds
