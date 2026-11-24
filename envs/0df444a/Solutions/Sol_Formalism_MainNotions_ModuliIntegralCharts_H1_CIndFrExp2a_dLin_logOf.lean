-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a.dLin_logOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:42:46.018299+00:00
-- url     : https://prove2.me/submissions/2990eebd-b44a-4768-b5a3-bca8ee3a84be

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_low_subst__b3c6c3b879e6
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.FG.SolveVAux Formalism.L2.Pj
variable {S : Type} [CommRing S]
variable [Algebra ℚ S] {d : ℕ}
private lemma low_two_of_lemma {σ : Type} {f : MvPowerSeries σ S} (h0 : constantCoeff f = 0)
    (h1 : ∀ w, coeff (Finsupp.single w 1) f = 0) : Low 2 f := by
  classical
  intro e he
  by_cases hz : e = 0
  · subst hz
    rw [coeff_zero_eq_constantCoeff_apply]
    exact h0
  · obtain ⟨w, hw⟩ := Finsupp.support_nonempty_iff.mpr hz
    have hdeg : e.degree = ∑ s ∈ e.support, e s := rfl
    rw [hdeg] at he
    have hw1 : 1 ≤ e w := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hw)
    have hwle : e w ≤ ∑ s ∈ e.support, e s := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw
    have hew : e w = 1 := by omega
    have hv : ∀ v, v ≠ w → e v = 0 := by
      intro v hvw
      by_contra hne
      have hvs : v ∈ e.support := Finsupp.mem_support_iff.mpr hne
      have hsub : ({v, w} : Finset σ) ⊆ e.support :=
        Finset.insert_subset_iff.mpr ⟨hvs, Finset.singleton_subset_iff.mpr hw⟩
      have hle := Finset.sum_le_sum_of_subset (f := fun s => e s) hsub
      rw [Finset.sum_pair hvw] at hle
      have hv1 : 1 ≤ e v := Nat.one_le_iff_ne_zero.mpr hne
      omega
    have he1 : e = Finsupp.single w 1 := by
      ext v
      by_cases hvw : v = w
      · subst hvw
        simp [hew]
      · rw [hv v hvw, Finsupp.single_apply, if_neg (Ne.symm hvw)]
    rw [he1]
    exact h1 w
private lemma cc_subst_lemma_2 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ S}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ S) :
    coeff 0 (subst a f) = coeff 0 f := by
  have ha : HasSubst a := ⟨fun s => by rw [ha0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hR : Low 1 (f - coeff 0 f • (1 : MvPowerSeries σ S)) := by
    rw [low_one_iff, ← coeff_zero_eq_constantCoeff_apply, map_sub, map_smul, coeff_zero_one, smul_eq_mul,
      mul_one, sub_self]
  have hS : Low 1 (subst a (f - coeff 0 f • (1 : MvPowerSeries σ S))) :=
    low_subst (fun s => (low_one_iff _).2 (ha0 s)) hR
  have hsub : subst a (f - coeff 0 f • (1 : MvPowerSeries σ S)) =
      subst a f - coeff 0 f • (1 : MvPowerSeries τ S) := by
    rw [← coe_substAlgHom ha, map_sub, map_smul, map_one]
  rw [hsub] at hS
  have h0 := hS 0 (by simp)
  rw [map_sub, map_smul, coeff_zero_one, smul_eq_mul, mul_one, sub_eq_zero] at h0
  exact h0
private lemma lin_subst_lemma_3 {σ τ : Type} [Fintype σ] {a : σ → MvPowerSeries τ S}
    (ha0 : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ S} (hf0 : constantCoeff f = 0) (w : τ) :
    coeff (Finsupp.single w 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single w 1) (a s) := by
  classical
  have ha : HasSubst a := ⟨fun s => by rw [ha0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hR : Low 2 (f - ∑ s, coeff (Finsupp.single s 1) f • X s) := by
    apply low_two_of_lemma
    · rw [← coeff_zero_eq_constantCoeff_apply, map_sub, map_sum]
      simp only [map_smul, coeff_zero_X, smul_zero, Finset.sum_const_zero, sub_zero]
      rw [coeff_zero_eq_constantCoeff_apply]
      exact hf0
    · intro v
      simp [coeff_X, Finsupp.single_left_inj Nat.one_ne_zero]
  have hS := low_subst' (fun s => (low_one_iff _).2 (ha0 s)) hR
  have hsplit : subst a f = subst a (f - ∑ s, coeff (Finsupp.single s 1) f • X s) +
      ∑ s, coeff (Finsupp.single s 1) f • a s := by
    rw [← coe_substAlgHom ha, map_sub, map_sum]
    simp only [map_smul]
    simp only [coe_substAlgHom, subst_X ha, sub_add_cancel]
  rw [hsplit, map_add, hS (Finsupp.single w 1) (by simp), zero_add, map_sum]
  simp only [map_smul, smul_eq_mul]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.FG.SolveVAux Formalism.L2.Pj
variable {S : Type} [CommRing S]
variable [Algebra ℚ S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
theorem _root_.solution (G : FGLaw S d) : ReciprocityTheory.ChartRestriction.G.TB.dLin (fun i => ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = 1 := by
  have hlin : ∀ i b : Fin d, coeff (Finsupp.single ((1 : Fin 2), b) 1) (G.F i) = if b = i then 1 else 0 := by
    intro i b
    have hu := congrArg (coeff (Finsupp.single ((0 : Fin 1), b) 1)) (G.unit i)
    have ha0 : ∀ p : Fin 2 × Fin d, constantCoeff ((![0, pt S d 0] : Fin 2 → Pt S 1 d) p.1 p.2) = 0 := by
      rintro ⟨a, j⟩
      fin_cases a <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
    change coeff _ (subst (fun p : Fin 2 × Fin d => (![0, pt S d 0] : Fin 2 → Pt S 1 d) p.1 p.2) (G.F i)) = _
      at hu
    rw [lin_subst_lemma_3 ha0 (G.const i), Fintype.sum_prod_type, Fin.sum_univ_two] at hu
    simpa [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, coeff_X, Finsupp.single_left_inj Nat.one_ne_zero] using hu
  have hJ : ∀ i b : Fin d, constantCoeff (ReciprocityTheory.ChartRestriction.G.TB.LogPf.Jac G i b) = if i = b then 1 else 0 := by
    intro i b
    have ha0 : ∀ p : Fin 2 × Fin d, constantCoeff ((![pt S d 0, 0] : Fin 2 → Pt S 1 d) p.1 p.2) = 0 := by
      rintro ⟨a, j⟩
      fin_cases a <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
    change constantCoeff (subst (fun p : Fin 2 × Fin d => (![pt S d 0, 0] : Fin 2 → Pt S 1 d) p.1 p.2)
      (pderiv S ((1 : Fin 2), b) (G.F i))) = _
    rw [← coeff_zero_eq_constantCoeff_apply, cc_subst_lemma_2 ha0, coeff_pderiv, zero_add, hlin i b]
    by_cases h : i = b
    · subst h
      simp
    · simp [h, Ne.symm h]
  have hM : (ReciprocityTheory.ChartRestriction.G.TB.LogPf.JM G).map constantCoeff = 1 := by
    ext i b
    rw [Matrix.map_apply, Matrix.one_apply]
    exact hJ i b
  have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.TB.LogPf.JM G).det := by
    rw [isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, hM, Matrix.det_one]
    exact isUnit_one
  have hOm : (ReciprocityTheory.ChartRestriction.G.TB.LogPf.Om G).map constantCoeff = 1 := by
    have h1 := congrArg (fun A : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin 1 × Fin d) S) => A.map constantCoeff)
      (Matrix.mul_nonsing_inv _ hdet)
    simp only [Matrix.map_mul, hM, Matrix.one_mul, Matrix.map_one, map_zero, map_one] at h1
    exact h1
  ext i j
  have hcoef : coeff (Finsupp.single ((0 : Fin 1), j) 1) (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) =
      constantCoeff (ReciprocityTheory.ChartRestriction.G.TB.LogPf.Om G i j) := by
    show algebraMap ℚ S (((Finsupp.degree (Finsupp.single ((0 : Fin 1), j) (1 : ℕ)) : ℕ) : ℚ)⁻¹) * _ = _
    rw [Finset.sum_eq_single ((0 : Fin 1), j)]
    · simp [coeff_zero_eq_constantCoeff_apply]
    · intro w _ hw
      simp [Finsupp.single_apply, Ne.symm hw]
    · intro h
      exact absurd (Finset.mem_univ _) h
  show coeff (Finsupp.single ((0 : Fin 1), j) 1) (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = (1 : Matrix (Fin d) (Fin d) S) i j
  rw [hcoef]
  have h2 : ((ReciprocityTheory.ChartRestriction.G.TB.LogPf.Om G).map constantCoeff) i j = (1 : Matrix (Fin d) (Fin d) S) i j := by
    rw [hOm]
  rw [Matrix.map_apply] at h2
  exact h2
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
