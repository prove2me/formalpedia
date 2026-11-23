-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.generic_minor_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:07.74842+00:00
-- url     : https://prove2.me/submissions/1c78f6ff-5f6d-4a53-bdc9-89abd7d5ad7a

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Generic
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_generic_mono_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] {l d N0 n : ℕ} (hl : l.Prime)
    (Y : ZMod d × Fin N0 × Fin N0 → K) (hY : IsGeneric l Y) (s : ZMod d) (z : Fin N0)
    (t : Fin n → ZMod d) (L : Fin n → ℕ) (e : Fin n → Fin N0) (he : Function.Injective e)
    (hn : n ≤ N0) (hts : ∀ i, t i ≠ s) (hL : ∀ i, L i ≠ 0)
    (hinj : Function.Injective fun i => (t i, L i)) :
    ‖(Matrix.of fun (i i' : Fin n) => ∑ a, Y (t i, z, a) ^ (L i) * Y (s, e i', a)).det‖ = 1 := by
  classical
  haveI : Fact (1 < l) := ⟨hl.one_lt⟩
  set P : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℤ := (Matrix.of fun (i i' : Fin n) =>
    ∑ a, MvPolynomial.X (t i, z, a) ^ (L i) * MvPolynomial.X (s, e i', a)).det with hP
  have hev : MvPolynomial.aeval Y P
      = (Matrix.of fun (i i' : Fin n) => ∑ a, Y (t i, z, a) ^ (L i) * Y (s, e i', a)).det := by
    rw [hP, AlgHom.map_det]
    congr 1
    ext i i'
    simp
  rw [← hev]
  refine hY P ?_
  intro h0
  have hmap : MvPolynomial.map (Int.castRingHom (ZMod l)) P = (Matrix.of fun (i i' : Fin n) =>
      ∑ a, (MvPolynomial.X (t i, z, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L i)
        * MvPolynomial.X (s, e i', a)).det := by
    rw [hP, RingHom.map_det]
    congr 1
    ext i i'
    simp
  rw [hmap] at h0
  let f : ZMod d × Fin N0 × Fin N0 → MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l) :=
    fun v => if v.1 = s then (if v.2.1 = v.2.2 then 1 else 0) else MvPolynomial.X v
  have h1 := congrArg (MvPolynomial.bind₁ f) h0
  rw [map_zero, AlgHom.map_det] at h1
  have h2 : (MvPolynomial.bind₁ f).mapMatrix (Matrix.of fun (i i' : Fin n) =>
      ∑ a, (MvPolynomial.X (t i, z, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L i)
        * MvPolynomial.X (s, e i', a))
      = Matrix.of fun (r c : Fin n) =>
        (MvPolynomial.X (t r, z, e c) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L r) := by
    ext i i'
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, map_pow,
      MvPolynomial.bind₁_X_right, f, if_neg (hts i), if_true]
    rw [Finset.sum_eq_single (e i')]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · simp
  rw [h2] at h1
  exact generic_mono_det z t L e he hL hinj h1
end Formalism.DworkPowerSeriesWeights
