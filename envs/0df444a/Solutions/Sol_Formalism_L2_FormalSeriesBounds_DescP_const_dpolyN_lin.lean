-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.DescP.const_dpolyN_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:14.312499+00:00
-- url     : https://prove2.me/submissions/03cf5486-48ce-42ea-84f3-1605f2cceda8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_dpolyN_sub

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.DescP
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {n d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.DescP
theorem _root_.solution (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    {α : Type} (s : Finset α) (c : α → k) (Q : α → MvPolynomial ι k) (g : PS k n d) :
    constantCoeff (DpolyN F cp u (∑ i ∈ s, c i • Q i) g) =
      ∑ i ∈ s, c i * constantCoeff (DpolyN F cp u (Q i) g) := by
  set S := (∑ i ∈ s, c i • Q i).support ∪ s.biUnion (fun i => (Q i).support) with hS
  rw [dpolyN_sub F cp u _ g S Finset.subset_union_left]
  have hQ : ∀ i ∈ s, DpolyN F cp u (Q i) g = ∑ m ∈ S, MvPowerSeries.C ((Q i).coeff m) * DmonN F cp u m g :=
    fun i hi => dpolyN_sub F cp u _ g S
      (fun m hm => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, hm⟩))
  have hR : ∑ i ∈ s, c i * constantCoeff (DpolyN F cp u (Q i) g) =
      ∑ i ∈ s, c i * constantCoeff (∑ m ∈ S, MvPowerSeries.C ((Q i).coeff m) * DmonN F cp u m g) :=
    Finset.sum_congr rfl fun i hi => by rw [hQ i hi]
  rw [hR]
  simp only [map_sum, map_mul, MvPowerSeries.constantCoeff_C, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
end Formalism.L2.FormalSeriesBounds.DescP
