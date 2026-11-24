-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.sizesSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:55:12.754241+00:00
-- url     : https://prove2.me/submissions/247eb95b-ae86-425e-b787-80132bae6bbc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_rd_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_block_lattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_degreeFacts_statement
import Theorems.Thm_Formalism_FourierDecayAlt_P_dualIdealEqLiftIdeal
import Theorems.Thm_Formalism_FourierDecayAlt_P_lattice_facts_general
import Theorems.Thm_Formalism_FourierDecayAlt_P_scaledIdealNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBC
open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped Pointwise
noncomputable section
open Classical
open Formalism.FourierDecayAlt.P.PBC.Lat
namespace Formalism.FourierDecayAlt.P.PBC.Lat
theorem _root_.solution : PBC.SizesSup := by
  intro Cs hCs
  refine ⟨Cs, hCs, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ S hg1 hg2 hU b n hb hn hthr
  obtain ⟨-, hcard, hdeg⟩ := Formalism.FourierDecayAlt.P.degreeFacts_statement E
  have hf : S.f = S6.deg E := by
    rw [← hcard, ← Fintype.card_fin S.f]; exact Fintype.card_congr S.pl
  have hfpos : 0 < S.f := hf ▸ hdeg
  have : Nonempty (Fin S.f) := ⟨⟨0, hfpos⟩⟩
  have hgN : 0 < S.g := Nat.mul_pos hg1 hg2
  have hg1R : (1 : ℝ) ≤ S.g := by exact_mod_cast hgN
  have hgR : (0 : ℝ) < S.g := by linarith
  have hrd1 := rd_ge_one E
  have hrd : 0 < S6.rd E := by linarith
  obtain ⟨-, -, -, -, -, -, hN, -⟩ := Formalism.FourierDecayAlt.P.block_lattices Formalism.FourierDecayAlt.P.lattice_facts_general
    Formalism.FourierDecayAlt.P.dualIdealEqLiftIdeal Formalism.FourierDecayAlt.P.scaledIdealNorm E hU S.g S.G.r b n hgN
  set ν : ℤ := S6.nuBlock S.G.r b n with hν
  set x : ℝ := S6.rd E ^ ν with hx
  have hxpos : 0 < x := zpow_pos hrd _
  have hexp : ((2 * S.G.r + 4 : ℤ) - 2 * b - n) = ν + 1 := by
    simp only [hν, S6.nuBlock]; ring
  rw [hexp, zpow_add₀ hrd.ne', zpow_one] at hN
  set m : ℝ := Finset.univ.inf' Finset.univ_nonempty (thr S b n) with hm
  have hmpos : 0 < m := by
    rw [hm, Finset.lt_inf'_iff]; exact fun v _ => hthr v
  have hmle : ∀ v, m ≤ thr S b n v := fun v => Finset.inf'_le _ (Finset.mem_univ v)
  refine ⟨S.g / m, div_pos hgR hmpos, ?_⟩
  set R : ℝ := S.g / m with hR
  have hRpos : 0 < R := div_pos hgR hmpos

  set Nn : ℝ := (FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ) with hNn
  have hNn0 : 0 ≤ Nn := by
    have : 0 < √Nn := by rw [hN]; positivity
    exact (Real.sqrt_pos.mp this).le
  have hNinv : Nn⁻¹ = ((S.g : ℝ) * (x * S6.rd E)) ^ (2 * S.f) := by
    have h2 : Nn = (√Nn) ^ 2 := (Real.sq_sqrt hNn0).symm
    rw [h2, hN, ← hf]
    rw [inv_pow, inv_inv, ← pow_mul, mul_comm S.f 2]

  have hvol : S.base.vol b n = (∏ v, thr S b n v) ^ 2 * Nn⁻¹ := by
    simp only [C.HidaSetting.base, C.HidaSetting.mkData, thr]
    rw [div_eq_mul_inv]
    congr 2
    exact (Equiv.prod_comp S.pl (fun w => J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b n w)).symm
  have hdlB : KB.dlB S b n = x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) := by
    have e : S6.rd E ^ (2 * ν) = x ^ 2 := by rw [hx, ← zpow_natCast, ← zpow_mul]; ring_nf
    simp only [KB.dlB, D.deG]
    rw [← hν, e]
    field_simp
  rw [hvol, hNinv, hdlB]

  have key : ∀ v, x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * (Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ 2 ≤
      Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) := by
    intro v
    have ht := hthr v
    have h1 : (1 + (R * thr S b n v / S.g) ^ 2) / R ^ 2 ≤ 2 * thr S b n v ^ 2 / (S.g : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hR' : R * m = S.g := by rw [hR]; field_simp
      have hmt : m ^ 2 ≤ thr S b n v ^ 2 := pow_le_pow_left₀ hmpos.le (hmle v) 2
      have : (S.g : ℝ) ^ 2 ≤ R ^ 2 * thr S b n v ^ 2 := by
        rw [← hR']; nlinarith [sq_nonneg R]
      have e : (1 + (R * thr S b n v / S.g) ^ 2) * (S.g : ℝ) ^ 2 =
          (S.g : ℝ) ^ 2 + R ^ 2 * thr S b n v ^ 2 := by field_simp
      rw [e] <;> nlinarith
    calc x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * (Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ 2
        = x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * Cs * ((1 + (R * thr S b n v / S.g) ^ 2) / R ^ 2) := by ring
      _ ≤ x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * Cs * (2 * thr S b n v ^ 2 / (S.g : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) * (1 / ((S.g : ℝ) * S6.rd E)) := by
          field_simp
      _ ≤ Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by positivity)] <;> nlinarith
      _ = _ := mul_one _
  calc (∏ _v : Fin S.f, x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2)) *
        (∏ v, Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ (2 * S.f)
      = ∏ v, x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * (Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ 2 := by
        conv_rhs => rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [pow_mul]
    _ ≤ ∏ v, Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) :=
        Finset.prod_le_prod (fun v _ => by have := hthr v; positivity) (fun v _ => key v)
    _ = Cs ^ S.f * ((∏ v, thr S b n v) ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ (2 * S.f)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← pow_mul, mul_comm 2 S.f]
end Formalism.FourierDecayAlt.P.PBC.Lat
