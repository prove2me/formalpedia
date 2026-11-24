-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusScale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:10.132993+00:00
-- url     : https://prove2.me/submissions/42810a2b-3ef2-4589-b3aa-4d7c294041f2

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusScale_span
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusScale_transfer
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_mem_one_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField
noncomputable section
namespace Formalism.HermitianLatticesTheory
section SlopeTestRemainingChoices
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end SlopeTestRemainingChoices
private theorem exists_nat_pos_mul_mem_one {K : Type} [Field K] [NumberField K] (z : K) :
    ∃ n : ℕ, 0 < n ∧ (n : K) * z ∈ (1 : Submodule (𝓞 K) K) := by
  have hz : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsIntegral.isIntegral (R := ℚ) z).isAlgebraic
  obtain ⟨y, hy0, hy⟩ := hz.exists_integral_multiple
  have hw : IsIntegral ℤ ((y.natAbs : K) * z) := by
    rcases Int.natAbs_eq y with e | e
    · rw [← Int.cast_natCast, ← e, ← zsmul_eq_mul]
      exact hy
    · have e' : (y.natAbs : ℤ) = -y := by linarith
      rw [← Int.cast_natCast, e', Int.cast_neg, neg_mul, ← zsmul_eq_mul]
      exact hy.neg
  exact ⟨y.natAbs, Int.natAbs_pos.mpr hy0, Submodule.mem_one.mpr ⟨⟨_, hw⟩, rfl⟩⟩
end Formalism.HermitianLatticesTheory
end
end

set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : GenusScale := by
  intro K V _ _ _ _ _ _ _ _ h _ L hL
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective _ _
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
    intro r
    have hr : IsIntegral ℤ (algebraMap (𝓞 K) K r) := NumberField.RingOfIntegers.isIntegral_coe r
    exact ⟨⟨star (algebraMap (𝓞 K) K r), hr.map (starRingEnd K).toIntAlgHom⟩, rfl⟩
  obtain ⟨s, hs⟩ := hL.fg
  choose n hn0 hn using exists_nat_pos_mul_mem_one (K := K)
  refine ⟨∏ q ∈ s ×ˢ s, n (h q.1 q.2), Finset.prod_pos (fun q _ => hn0 _), ?_⟩
  have hLd : ∀ x ∈ L, ∀ y ∈ L,
      ((∏ q ∈ s ×ˢ s, n (h q.1 q.2) : ℕ) : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
    rw [← hs]
    refine genusScale_span hinj hstar h _ _ ?_
    intro a ha b hb
    have hmem : (a, b) ∈ s ×ˢ s := Finset.mem_product.mpr ⟨ha, hb⟩
    obtain ⟨k, hk⟩ : n (h a b) ∣ ∏ q ∈ s ×ˢ s, n (h q.1 q.2) :=
      Finset.dvd_prod_of_mem (fun q : V × V => n (h q.1 q.2)) hmem
    rw [hk, Nat.cast_mul, mul_comm ((n (h a b) : ℕ) : K), mul_assoc]
    have hm := genusBasic_mem_one_mul _ (hn (h a b)) (k : 𝓞 K)
    rwa [map_natCast] at hm
  intro M hM x hx y hy
  have hM' : Submodule.IsLattice K M ∧ SameGenus h L M := hM
  exact genusScale_transfer hinj hstar h _ L M hM'.2 hLd x hx y hy
end Formalism.HermitianLatticesTheory
