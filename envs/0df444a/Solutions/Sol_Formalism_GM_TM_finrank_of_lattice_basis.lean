-- Prove2me | solution 1 for Formalism.GM.TM.finrank_of_lattice_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:28:14.184925+00:00
-- url     : https://prove2.me/submissions/870f5e18-e6d3-4b36-993f-6a91555c5f24

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_exists_pow_smul_intPol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.TM
theorem _root_.solution {σ : Type} (S : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) {n₀ : ℕ}
    (f : Fin n₀ → MvPolynomial σ ℚ_[p]) (hli : LinearIndependent ℤ_[p] f)
    (hsp : Submodule.span ℤ_[p] (Set.range f) = S.restrictScalars ℤ_[p] ⊓ IntPol p σ) :
    Module.finrank ℚ_[p] S = n₀ := by
  have hli' : LinearIndependent ℚ_[p] f := (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp hli
  have hS : Submodule.span ℚ_[p] (Set.range f) = S := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      have : f b ∈ Submodule.span ℤ_[p] (Set.range f) := Submodule.subset_span ⟨b, rfl⟩
      rw [hsp] at this
      exact (Submodule.mem_inf.mp this).1
    · intro x hx
      obtain ⟨k, hk⟩ := exists_pow_smul_intPol x
      have h1 : ((p : ℚ_[p]) ^ k) • x ∈ Submodule.span ℤ_[p] (Set.range f) := by
        rw [hsp]; exact Submodule.mem_inf.mpr ⟨S.smul_mem _ hx, hk⟩
      have h2 := Submodule.span_le_restrictScalars ℤ_[p] ℚ_[p] (Set.range f) h1
      have hp0 : ((p : ℚ_[p]) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
      have : x = ((p : ℚ_[p]) ^ k)⁻¹ • (((p : ℚ_[p]) ^ k) • x) := by
        rw [smul_smul, inv_mul_cancel₀ hp0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ h2
  rw [← hS, finrank_span_eq_card hli', Fintype.card_fin]
end Formalism.GM.TM
