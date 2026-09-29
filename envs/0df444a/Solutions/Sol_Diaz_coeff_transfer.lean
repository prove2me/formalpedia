-- Prove2me | solution 1 for Diaz.coeff_transfer
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:10.181932+00:00
-- url     : https://prove2.me/submissions/a7e43ae1-ec62-46f8-8597-61f1465561c6

import Mathlib


section
open ComplexConjugate
variable {K : Subfield ℂ} {u t : ℂ}

theorem solution (Φ : ℂ →+* ℂ) (hK : ∀ a ∈ K, Φ a = a)
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (w : Fin m → ℂ) (v : Fin n → ℂ)
    (hw : ∀ i, w i ∈ K) (hv : ∀ j, v j ∈ K) :
    Φ (∑ i, ∑ j, w i * M i j * v j) = ∑ i, ∑ j, w i * (Φ (M i j)) * v j := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, hK _ (hw i), hK _ (hv j)]
end
