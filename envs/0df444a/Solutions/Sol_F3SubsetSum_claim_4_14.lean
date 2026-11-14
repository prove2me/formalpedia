-- Prove2me | solution 1 for F3SubsetSum.claim_4_14
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T20:47:52.832524+00:00
-- url     : https://prove2.me/submissions/0fd064bd-5abd-4de6-9676-e0021fa4cee8

import Definitions.Def_F3SubsetSum_SampleImage
import Definitions.Def_F3SubsetSum_SymbolicRank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod

open F3SubsetSum

theorem solution (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n D : ℕ) (hD : 2 ≤ D) {t : ℕ}
    (a : Fin t → Fin n → ZMod q) (a' : Fin n → ZMod q) :
    (sampleImage q (Fin.snoc a a') D).dualAnnihilator =
        (LinearMap.ker ((contraction (ZMod q) n q D a').domRestrict
            (sampleImage q a D).dualAnnihilator)).map
          (sampleImage q a D).dualAnnihilator.subtype ∧
      increment q a a' D =
        Module.finrank (ZMod q) (LinearMap.range ((contraction (ZMod q) n q D a').domRestrict
          (sampleImage q a D).dualAnnihilator)) := by
  classical
  -- The linear algebra works independently of the two numerical lower bounds.
  clear hq hD
  let M := mulMap (ZMod q) n q (linForm a' ^ 2) (D - 2) D
  let V := sampleImage q a D
  let V' := sampleImage q (Fin.snoc a a') D
  let C := contraction (ZMod q) n q D a'
  let T := C.domRestrict V.dualAnnihilator

  -- Split the defining sum for Φ at the newly appended sample.
  have splitPhi (Q : Fin (t + 1) → Rd (ZMod q) n q (D - 2)) :
      Phi (ZMod q) q (Fin.snoc a a') D Q =
        Phi (ZMod q) q a D (fun i => Q i.castSucc) + M (Q (Fin.last t)) := by
    simp only [Phi, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, M]
  have imageStep : V' = V ⊔ LinearMap.range M := by
    apply le_antisymm
    · rintro _ ⟨Q, rfl⟩
      rw [splitPhi]
      exact Submodule.mem_sup.mpr
        ⟨_, ⟨fun i => Q i.castSucc, rfl⟩, _, ⟨Q (Fin.last t), rfl⟩, rfl⟩
    · intro x hx
      obtain ⟨_, ⟨Q, rfl⟩, _, ⟨R, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
      refine ⟨Fin.snoc Q R, ?_⟩
      rw [splitPhi]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]

  have kernelStep : V'.dualAnnihilator =
      (LinearMap.ker T).map V.dualAnnihilator.subtype := by
    calc
      V'.dualAnnihilator = V.dualAnnihilator ⊓ (LinearMap.range M).dualAnnihilator := by
        rw [imageStep, Submodule.dualAnnihilator_sup_eq]
      _ = V.dualAnnihilator ⊓ LinearMap.ker C := by
        change _ = V.dualAnnihilator ⊓ LinearMap.ker M.dualMap
        rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range]
      _ = (LinearMap.ker T).map V.dualAnnihilator.subtype := by
        dsimp only [T]
        rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]

  refine ⟨kernelStep, ?_⟩
  change (Module.finrank (ZMod q) (Rd (ZMod q) n q D) - Module.finrank (ZMod q) V) -
    (Module.finrank (ZMod q) (Rd (ZMod q) n q D) - Module.finrank (ZMod q) V') =
      Module.finrank (ZMod q) (LinearMap.range T)
  have oldDim := Subspace.finrank_add_finrank_dualAnnihilator_eq V
  have newDim := Subspace.finrank_add_finrank_dualAnnihilator_eq V'
  have kerDim : Module.finrank (ZMod q) V'.dualAnnihilator =
      Module.finrank (ZMod q) (LinearMap.ker T) := by
    rw [kernelStep, Submodule.finrank_map_subtype_eq]
  have rankNullity := LinearMap.finrank_range_add_finrank_ker (K := ZMod q)
    (V := ↥V.dualAnnihilator) (V₂ := Module.Dual (ZMod q) (Rd (ZMod q) n q (D - 2))) T
  omega
