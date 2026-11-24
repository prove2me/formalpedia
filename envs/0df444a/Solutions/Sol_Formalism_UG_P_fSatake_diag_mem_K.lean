-- Prove2me | solution 1 for Formalism.UG.P.fSatake_diag_mem_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:10.463101+00:00
-- url     : https://prove2.me/submissions/eeffe659-3045-4679-977b-a96cb31bdf92

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
namespace Formalism.UG.P
theorem _root_.solution {d : GU σ n} {e : Fin n → L} (hd : ⟪d⟫ = Matrix.diagonal e)
    (hd' : ⟪d⁻¹⟫ = Matrix.diagonal (fun i => (e i)⁻¹)) (hv : ∀ i, Valued.v (e i) = 1) :
    d ∈ KU σ n := by
  have hne : ∀ i, e i ≠ 0 := fun i h => by
    have h1 := hv i
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  have hint : ∀ i, e i ∈ intL L := fun i => by
    rw [intL]
    exact (Valuation.mem_integer_iff _ _).2 (hv i).le
  have hint' : ∀ i, (e i)⁻¹ ∈ intL L := fun i => by
    rw [intL]
    exact (Valuation.mem_integer_iff _ _).2 (by rw [map_inv₀, hv i, inv_one])
  let D : Matrix (Fin n) (Fin n) (intL L) := Matrix.diagonal fun i => ⟨e i, hint i⟩
  let D' : Matrix (Fin n) (Fin n) (intL L) := Matrix.diagonal fun i => ⟨(e i)⁻¹, hint' i⟩
  have h1 : D * D' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact Subtype.ext (by simp [hne i])
  have h2 : D' * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact Subtype.ext (by simp [hne i])
  rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf]
  refine ⟨d.2, ⟨⟨D, D', h1, h2⟩, ?_⟩⟩
  rw [bc]
  ext i j
  change ((intL L).subtype.mapMatrix D) i j = ⟪d⟫ i j
  rw [hd]
  by_cases hij : i = j
  · subst hij
    simp [D]
  · simp [D, Matrix.diagonal_apply_ne _ hij]
end Formalism.UG.P
