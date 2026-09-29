-- Prove2me | solution 1 for CuspForm.heckeAlgebra_ringHom_ext_of_primeFactors_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5beeb00e-dea2-5bc4-bbc1-68f50acec1e3

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeAlgebra_ringHom_ext_of_primeFactors_subset

theorem solution {N : ℕ} [NeZero N] {S : Set ℕ}
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    {R : Type} [CommRing R]
    (θ₁ θ₂ : CuspForm.heckeAlgebra N 2 S →+* R)
    (h : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      θ₁ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = θ₂ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) :
    θ₁ = θ₂ := by
  apply RingHom.toIntAlgHom_injective
  refine AlgHom.ext_of_eq_adjoin (S := CuspForm.heckeAlgebra N 2 S)
    (s := CuspForm.heckeGenerators N 2 S) rfl fun x hx => ?_
  rcases hx with ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩
  · exact h ℓ hℓ hℓN hℓS
  · exact absurd (hNS q hq hqN) hqS

end S_CuspForm_heckeAlgebra_ringHom_ext_of_primeFactors_subset
end P2MW
export P2MW.S_CuspForm_heckeAlgebra_ringHom_ext_of_primeFactors_subset (solution)
