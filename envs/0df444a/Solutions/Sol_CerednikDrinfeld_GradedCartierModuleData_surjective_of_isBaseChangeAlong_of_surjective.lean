-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.surjective_of_isBaseChangeAlong_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/30f5eca6-c4fd-54ff-98be-466b6fc2a661

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_surjective_of_isBaseChangeAlong_of_surjective

set_option autoImplicit false

namespace NFSurjProof

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [hp : Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
variable {j : Zp2 p →+* B} {φ : B →+* B'}
variable {D : GradedCartierModuleData p B j} {D' : GradedCartierModuleData p B' (φ.comp j)}

theorem iterate_verschiebung_add (E : GradedCartierModuleData p B j) (N : ℕ) (a b : E.M) :
    (⇑E.verschiebung)^[N] (a + b) = (⇑E.verschiebung)^[N] a + (⇑E.verschiebung)^[N] b := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih, map_add]

theorem map_iterate_verschiebung {f : D.M →+ D'.M} (hf : IsBaseChangeAlong φ D D' f) (N : ℕ)
    (x : D.M) : f ((⇑D.verschiebung)^[N] x) = (⇑D'.verschiebung)^[N] (f x) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hf.2.2.1, ih]

end NFSurjProof

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData NFSurjProof in
theorem solution
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
    (j : CerednikDrinfeld.Zp2 p →+* B) (φ : B →+* B') (hφ : Function.Surjective φ)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' (φ.comp j)) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D D' f) :
    Function.Surjective f := by
  classical
  obtain ⟨γ, hγ, hγ'⟩ := hf.2.2.2.2.2
  intro y'

  let step : D'.M → (Fin 2 → B') × D'.M := fun y => (hγ'.2 y).exists.choose
  have step_spec : ∀ y : D'.M,
      y = (∑ i : Fin 2, WittVector.teichmuller p ((step y).1 i) • f (γ i)) +
        D'.verschiebung (step y).2 :=
    fun y => (hγ'.2 y).exists.choose_spec

  let tail : ℕ → D'.M := fun n => (fun y => (step y).2)^[n] y'
  have tail_zero : tail 0 = y' := rfl
  have tail_succ : ∀ n, tail (n + 1) = (step (tail n)).2 := fun n =>
    Function.iterate_succ_apply' _ n y'
  let digit : ℕ → Fin 2 → B' := fun n => (step (tail n)).1

  let x' : ℕ → D'.M := fun n => ∑ i : Fin 2, WittVector.teichmuller p (digit n i) • f (γ i)
  have hy' : ∀ N : ℕ, y' = (∑ m ∈ Finset.range N, (⇑D'.verschiebung)^[m] (x' m)) +
      (⇑D'.verschiebung)^[N] (tail N) := by
    intro N
    induction N with
    | zero => simp [tail_zero]
    | succ N ih =>
      have hstep : tail N = x' N + D'.verschiebung (tail (N + 1)) := by
        rw [tail_succ]; exact step_spec (tail N)
      rw [Finset.sum_range_succ, Function.iterate_succ_apply, add_assoc,
        ← iterate_verschiebung_add, ← hstep]
      exact ih

  let lift : B' → B := fun b => (hφ b).choose
  have lift_spec : ∀ b, φ (lift b) = b := fun b => (hφ b).choose_spec
  let x : ℕ → D.M := fun n => ∑ i : Fin 2, WittVector.teichmuller p (lift (digit n i)) • γ i
  have hfx : ∀ n, f (x n) = x' n := by
    intro n
    simp only [x, x', map_sum, hf.1, WittVector.map_teichmuller, lift_spec]
  obtain ⟨s, hs, -⟩ := hD.2 x
  refine ⟨s, ?_⟩

  obtain ⟨s', -, huniq⟩ := hD'.2 x'
  have h1 : f s = s' := huniq _ (fun N => by
    obtain ⟨t, ht⟩ := hs N
    refine ⟨f t, ?_⟩
    rw [ht, map_add, map_sum, map_iterate_verschiebung hf]
    congr 1
    exact Finset.sum_congr rfl (fun m _ => by rw [map_iterate_verschiebung hf, hfx]))
  have h2 : y' = s' := huniq _ (fun N => ⟨tail N, hy' N⟩)
  rw [h1, h2]

end S_CerednikDrinfeld_GradedCartierModuleData_surjective_of_isBaseChangeAlong_of_surjective
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_surjective_of_isBaseChangeAlong_of_surjective (solution)
