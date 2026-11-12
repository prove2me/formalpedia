-- Prove2me | solution 2 for BunkbedFalse.robust_hyperedge
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T03:27:36.222009+00:00
-- url     : https://prove2.me/submissions/04467996-4b79-4641-9964-44a916fb04f0

import Theorems.Thm_BunkbedAux_cancel_on_X
import Theorems.Thm_BunkbedAux_xc_block_pos
import Theorems.Thm_BunkbedAux_wzProb_pair_sum
open Bunkbed Bunkbed.Hyper Bunkbed.Hyper.WZExt Finset SimpleGraph

private lemma wz_sum {M : Type*} [AddCommMonoid M] (f : WZ → M) :
    ∑ s : WZ, f s = f .abc + f .ab_c + f .ac_b + f .a_bc + f .a_b_c := by
  show Finset.sum {WZ.abc, WZ.ab_c, WZ.ac_b, WZ.a_bc, WZ.a_b_c} f = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

private lemma fibre_sum (P : WZ → ℚ) (a b : WZ) :
    ∑ q ∈ univ.filter (fun q : WZExt => legal q = true ∧ toPair q = (a, b)), wt P q
      = P a * P b := by
  rw [Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [wz_sum, Fin.sum_univ_four]
  cases a <;> cases b <;> simp [wt, toPair, legal] <;> ring

private lemma refined6 (P : WZ → ℚ) (g : (Fin 6 → WZ × WZ) → ℚ) :
    ∑ Ψ ∈ univ.filter (fun Ψ : Fin 6 → WZExt => ∀ i, legal (Ψ i) = true),
        (∏ i, wt P (Ψ i)) * g (fun i => toPair (Ψ i))
      = ∑ φ : Fin 6 → WZ × WZ, (∏ i, P (φ i).1 * P (φ i).2) * g φ := by
  have hmaps : ∀ Ψ ∈ univ.filter (fun Ψ : Fin 6 → WZExt => ∀ i, legal (Ψ i) = true),
      (fun i => toPair (Ψ i)) ∈ (univ : Finset (Fin 6 → WZ × WZ)) := fun Ψ _ => mem_univ _
  have key := Finset.sum_fiberwise_of_maps_to hmaps
      (fun Ψ : Fin 6 → WZExt => (∏ i, wt P (Ψ i)) * g (fun i => toPair (Ψ i)))
  rw [← key]
  refine Finset.sum_congr rfl (fun φ _ => ?_)
  have hset : (univ.filter (fun Ψ : Fin 6 → WZExt => ∀ i, legal (Ψ i) = true)).filter
        (fun Ψ => (fun i => toPair (Ψ i)) = φ)
      = Fintype.piFinset
          (fun i => univ.filter (fun q : WZExt => legal q = true ∧ toPair q = φ i)) := by
    ext Ψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, funext_iff]
    exact ⟨fun ⟨hl, hp⟩ i => ⟨hl i, hp i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  rw [hset]
  have hconst : ∀ Ψ ∈ Fintype.piFinset
      (fun i => univ.filter (fun q : WZExt => legal q = true ∧ toPair q = φ i)),
      (∏ i, wt P (Ψ i)) * g (fun i => toPair (Ψ i)) = (∏ i, wt P (Ψ i)) * g φ := by
    intro Ψ hΨ
    have harg : (fun i => toPair (Ψ i)) = φ := by
      funext i
      exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hΨ i)).2.2
    rw [harg]
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul, ← Finset.prod_univ_sum]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => fibre_sum P (φ i).1 (φ i).2)

private lemma wzOfExt_def (Ψ : Fin 6 → WZExt) :
    (fun p : Fin 6 × Fin 2 => if p.2 = 0 then (toPair (Ψ p.1)).1 else (toPair (Ψ p.1)).2)
      = wzOfExt Ψ := rfl

private noncomputable def ind (y : Fin 10 × Fin 2) (Ψ : Fin 6 → WZExt) : ℚ :=
  if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable ((0 : Fin 10), (0 : Fin 2)) y
  then (1 : ℚ) else 0

private lemma setX :
    (univ.filter (fun Ψ : Fin 6 → WZExt => ∀ i, legal (Ψ i) = true)).filter
      (fun Ψ => ∃ k, inLamSq (Ψ k) = true)
    = univ.filter (fun Ψ : Fin 6 → WZExt =>
        (∀ h, legal (Ψ h) = true) ∧ ∃ k, inLamSq (Ψ k) = true) := by
  ext Ψ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private lemma setXc :
    (univ.filter (fun Ψ : Fin 6 → WZExt => ∀ i, legal (Ψ i) = true)).filter
      (fun Ψ => ¬ ∃ k, inLamSq (Ψ k) = true)
    = univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ univ.filter (fun q : WZExt => legal q = true ∧ inLamSq q = false)) := by
  ext Ψ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, Bool.not_eq_true,
    forall_and]

set_option maxHeartbeats 2000000 in
theorem solution (P : WZ → ℚ)
    (hnn : ∀ s, 0 ≤ P s)
    (hsum : P .abc + P .a_b_c + P .a_bc + P .ab_c + P .ac_b = 1)
    (hsym : P .ab_c = P .ac_b)
    (hpos : 0 < P .abc * P .a_b_c - P .ab_c * P .ac_b)
    (h400 : 400 * P .a_bc ≤ P .abc * P .a_b_c - P .ab_c * P .ac_b) :
    wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2))
      < wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) := by
  have bridge : ∀ y : Fin 10 × Fin 2,
      wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) y
        = ∑ Ψ ∈ univ.filter (fun Ψ : Fin 6 → WZExt => ∀ i, legal (Ψ i) = true),
            (∏ i, wt P (Ψ i)) * ind y Ψ := by
    intro y
    refine (BunkbedAux.wzProb_pair_sum hollomTriple hollomT P
        ((0 : Fin 10), (0 : Fin 2)) y).trans ?_
    refine (refined6 P (fun φ : Fin 6 → WZ × WZ =>
      if (wzGraph hollomTriple hollomT
          (fun p => if p.2 = 0 then (φ p.1).1 else (φ p.1).2)).Reachable
        ((0 : Fin 10), (0 : Fin 2)) y then (1 : ℚ) else 0)).symm.trans ?_
    refine Finset.sum_congr rfl (fun Ψ _ => ?_)
    simp only [ind, wzOfExt_def]
  rw [bridge, bridge, ← sub_pos, ← Finset.sum_sub_distrib]
  have hre : ∀ Ψ : Fin 6 → WZExt,
      (∏ i, wt P (Ψ i)) * ind ((9 : Fin 10), (1 : Fin 2)) Ψ
        - (∏ i, wt P (Ψ i)) * ind ((9 : Fin 10), (0 : Fin 2)) Ψ
      = (∏ i, wt P (Ψ i)) * (ind ((9 : Fin 10), (1 : Fin 2)) Ψ
          - ind ((9 : Fin 10), (0 : Fin 2)) Ψ) := fun Ψ => by ring
  rw [Finset.sum_congr rfl (fun Ψ _ => hre Ψ),
    ← Finset.sum_filter_add_sum_filter_not _ (fun Ψ : Fin 6 → WZExt => ∃ k, inLamSq (Ψ k) = true),
    setX, setXc]
  have hX : ∑ Ψ ∈ univ.filter (fun Ψ : Fin 6 → WZExt =>
      (∀ h, legal (Ψ h) = true) ∧ ∃ k, inLamSq (Ψ k) = true),
      (∏ i, wt P (Ψ i)) * (ind ((9 : Fin 10), (1 : Fin 2)) Ψ
        - ind ((9 : Fin 10), (0 : Fin 2)) Ψ) = 0 := by
    rw [Finset.sum_congr rfl (fun Ψ _ => by rw [mul_sub]), Finset.sum_sub_distrib]
    simp only [ind]
    rw [BunkbedAux.cancel_on_X P, sub_self]
  rw [hX, zero_add]
  simpa only [ind] using BunkbedAux.xc_block_pos P hnn hsum hpos h400
