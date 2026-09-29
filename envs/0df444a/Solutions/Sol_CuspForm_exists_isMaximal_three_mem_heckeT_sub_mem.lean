-- Prove2me | solution 1 for CuspForm.exists_isMaximal_three_mem_heckeT_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4f8c4a91-f048-5475-a146-12488000d66c

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Theorems.Thm_EisensteinWeightOne_three_dvd_coeff_mul_e1Chi3_sub
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_isMaximal_three_mem_heckeT_sub_mem

open EisensteinWeightOne

lemma LaneB.e1Chi3In_int : e1Chi3In ℤ = e1Chi3 := by
  have : Int.castRingHom ℤ = RingHom.id ℤ := RingHom.ext_int _ _
  rw [e1Chi3In, this, PowerSeries.map_id]
  rfl

lemma LaneB.three_dvd_coeff_bridgeProduct_sub (a : ℕ → ℤ) (m : ℕ) :
    (3 : ℤ) ∣ PowerSeries.coeff m (bridgeProduct a) - a m := by
  have h := EisensteinWeightOne.three_dvd_coeff_mul_e1Chi3_sub (PowerSeries.mk a) m
  rw [PowerSeries.coeff_mk] at h
  simpa [bridgeProduct, LaneB.e1Chi3In_int] using h

theorem solution {N : ℕ} [NeZero N] {a : ℕ → ℤ}
    (h1 : a 1 = 1)
    (hT : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ, (3 : ℤ) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a))
    {M : Type*} [AddCommGroup M] [Module (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) M]
    (red : PowerSeries ℤ → M)
    (hker : ∀ g : PowerSeries ℤ, (∀ n, (3 : ℤ) ∣ PowerSeries.coeff n g) → red g = 0)
    (hker' : ∀ g : PowerSeries ℤ, red g = 0 → (3 : ℤ) ∣ PowerSeries.coeff 1 g)
    (h3M : (3 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) • red (bridgeProduct a) = 0)
    (hop : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      (CuspForm.heckeAlgebra.T hℓ hℓN hℓN - ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}))
          • red (bridgeProduct a)
        = red (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a)) :
    ∃ 𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}), 𝔪₁.IsMaximal ∧
      ((3 : ℕ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        CuspForm.heckeAlgebra.T hℓ hℓN hℓN - ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ := by
  classical
  set v := red (bridgeProduct a) with hv

  set S : Set (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) :=
    insert (3 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})
      {x | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        x = CuspForm.heckeAlgebra.T hℓ hℓN hℓN - ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})} with hS

  have hkill : ∀ s ∈ S, s • v = 0 := by
    intro s hs
    rcases Set.mem_insert_iff.mp hs with rfl | ⟨ℓ, hℓ, hℓN, rfl⟩
    · exact h3M
    · rw [hv, hop ℓ hℓ hℓN]
      exact hker _ (hT ℓ hℓ hℓN)

  have hv0 : v ≠ 0 := by
    intro h0
    have h3 : (3 : ℤ) ∣ PowerSeries.coeff 1 (bridgeProduct a) := hker' _ h0
    have h3' := LaneB.three_dvd_coeff_bridgeProduct_sub a 1
    rw [h1] at h3'
    have : (3 : ℤ) ∣ 1 := by
      have := dvd_sub h3 h3'
      simpa using this
    omega

  have hle : Ideal.span S ≤ Ideal.torsionOf (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) M v :=
    Ideal.span_le.mpr fun s hs => (Ideal.mem_torsionOf_iff v s).mpr (hkill s hs)
  have hne : Ideal.span S ≠ ⊤ := by
    intro htop
    have h1mem : (1 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ Ideal.torsionOf _ M v :=
      hle (htop ▸ Submodule.mem_top)
    rw [Ideal.mem_torsionOf_iff, one_smul] at h1mem
    exact hv0 h1mem
  obtain ⟨𝔪₁, h𝔪₁, h𝔪le⟩ := Ideal.exists_le_maximal _ hne
  refine ⟨𝔪₁, h𝔪₁, ?_, fun ℓ hℓ hℓN => ?_⟩
  · have : (3 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ Ideal.span S := Ideal.subset_span (Set.mem_insert _ _)
    simpa using h𝔪le this
  · exact h𝔪le (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr ⟨ℓ, hℓ, hℓN, rfl⟩)))

end S_CuspForm_exists_isMaximal_three_mem_heckeT_sub_mem
end P2MW
export P2MW.S_CuspForm_exists_isMaximal_three_mem_heckeT_sub_mem (solution)
