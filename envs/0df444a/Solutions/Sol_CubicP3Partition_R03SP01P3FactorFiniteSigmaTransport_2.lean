-- Prove2me | solution 2 for CubicP3Partition.R03SP01P3FactorFiniteSigmaTransport
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:28:28.587161+00:00
-- url     : https://prove2.me/submissions/918710d4-2053-40a6-b446-fa7a6488ec61

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_06d654dbb2_r03_sp01_finite_sigma_p3_factor_gluing_candidate

/-!
# Finite dependent-sum gluing for P3 factors

Candidate-only formalization for `problem:opg-46613-p3-partition`.
Bindings: problem contract SHA-256
`4a95f992a4ad0225a5d28b64ebb8172cfa123a0c75158e1c680f3266d16341dd`,
statement SHA-256
`3c1569b2adae0a7571fcd9b8ade6f0db66df27bc341cd2324fe28ab11f807dc0`,
attempt `attempt:opg46613-obligation-planning-v1`, graph
`graph:opg46613-obligations-v1`, and obligation
`obligation:r03-root-p3-factor`.

The theorem generalizes binary disjoint-sum gluing to an arbitrary finite
family of possibly dependent vertex types.  It only transports local edges
into an ambient graph; it does not assert that the summands are graph
components, choose a matching or 2-factor, or close the root.
-/

namespace CubicP3Partition

universe u v
set_option maxHeartbeats 1000000

theorem R03SP01P3FactorFiniteSigma
    {ι : Type u} [Fintype ι]
    {V : ι → Type v} [∀ i, Fintype (V i)]
    (Gi : ∀ i, SimpleGraph (V i))
    (G : SimpleGraph (Σ i, V i))
    (p : ∀ i, P3Factor (Gi i))
    (hAdj : ∀ (i : ι) {x y : V i}, (Gi i).Adj x y →
      G.Adj ⟨i, x⟩ ⟨i, y⟩) :
    Nonempty (P3Factor G) := by
  let total : Nat := ∑ i, (p i).blockCount
  let cardEq : Fintype.card (Σ i, Fin (p i).blockCount) = total := by
    simp [total, Fintype.card_sigma]
  let blockEquiv : Fin total ≃ (Σ i, Fin (p i).blockCount) :=
    (Equiv.cast (congrArg Fin cardEq.symm)).trans
      (Fintype.equivFin (Σ i, Fin (p i).blockCount)).symm
  let sourceEquiv : (Fin total × Fin 3) ≃
      (Σ i, (Fin (p i).blockCount × Fin 3)) :=
    (blockEquiv.prodCongr (Equiv.refl (Fin 3))).trans
      R03SP01SigmaProdDistrib
  let placeEquiv : (Σ i, (Fin (p i).blockCount × Fin 3)) ≃
      (Σ i, V i) :=
    Equiv.sigmaCongrRight (fun i => (p i).place)
  let place : (Fin total × Fin 3) ≃ (Σ i, V i) :=
    sourceEquiv.trans placeEquiv
  refine ⟨{
    blockCount := total
    place := place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro j
    let z : (Σ i, Fin (p i).blockCount) := blockEquiv j
    have hlocal : (Gi z.1).Adj
        ((p z.1).place (z.2, (0 : Fin 3)))
        ((p z.1).place (z.2, (1 : Fin 3))) :=
      (p z.1).edge01 z.2
    have hamb := hAdj z.1 hlocal
    simpa [place, placeEquiv, sourceEquiv, R03SP01SigmaProdDistrib, z] using hamb
  · intro j
    let z : (Σ i, Fin (p i).blockCount) := blockEquiv j
    have hlocal : (Gi z.1).Adj
        ((p z.1).place (z.2, (1 : Fin 3)))
        ((p z.1).place (z.2, (2 : Fin 3))) :=
      (p z.1).edge12 z.2
    have hamb := hAdj z.1 hlocal
    simpa [place, placeEquiv, sourceEquiv, R03SP01SigmaProdDistrib, z] using hamb


end CubicP3Partition

open CubicP3Partition
universe u v
theorem solution
    {ι : Type u} [Fintype ι]
    {V : ι → Type v} [∀ i, Fintype (V i)]
    {W : Type u} [Fintype W]
    (Gi : ∀ i, SimpleGraph (V i))
    (G : SimpleGraph W)
    (e : (Σ i, V i) ≃ W)
    (p : ∀ i, P3Factor (Gi i))
    (hAdj : ∀ (i : ι) {x y : V i}, (Gi i).Adj x y →
      G.Adj (e ⟨i, x⟩) (e ⟨i, y⟩)) :
    Nonempty (P3Factor G) := by
  let H : SimpleGraph (Σ i, V i) := G.comap e
  have hAdj' : ∀ (i : ι) {x y : V i}, (Gi i).Adj x y →
      H.Adj ⟨i, x⟩ ⟨i, y⟩ := by
    intro i x y hxy
    exact hAdj i hxy
  obtain ⟨q⟩ := R03SP01P3FactorFiniteSigma Gi H p hAdj'
  exact ⟨R03SP01P3FactorEquiv H G e (by intro x y h; exact h) q⟩
