-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.iso_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:18:00.36944+00:00
-- url     : https://prove2.me/submissions/ae701312-3ce5-4598-b913-4e8cec860415

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_qM_form
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_qM_fix
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_form_repr

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
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (c : K →+* K) (h : V → V → K)
variable {c h}
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
namespace Herm4
theorem _root_.solution (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (b : Basis n K V)
    (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0) (p q r s : n → K) (hp : ∀ i, c (p i) = p i) (hq : ∀ i, c (q i) = q i)
    (hr : ∀ i, c (r i) = r i) (hs : ∀ i, c (s i) = s i)
    (hsq : ∀ i, h (b i) (b i) = p i ^ 2 + q i ^ 2 + r i ^ 2 + s i ^ 2) :
    ∃ g : (Fin 4 → V) ≃ₗ[K] (Fin 4 × n → K), (∀ x y, ∑ w, g x w * c (g y w) = ∑ a, h (x a) (y a)) ∧
      ∀ x w, g x w = ∑ a, qM (p w.2) (q w.2) (r w.2) (s w.2) w.1 a * b.repr (x a) w.2 := by
  let Φ : (Fin 4 → V) →ₗ[K] (Fin 4 × n → K) :=
    { toFun := fun x w => ∑ a, qM (p w.2) (q w.2) (r w.2) (s w.2) w.1 a * b.repr (x a) w.2
      map_add' := by
        intro x y
        funext w
        simp [Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro k x
        funext w
        simp only [Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    funext a
    apply b.repr.injective
    ext i
    have hN : h (b i) (b i) ≠ 0 := (H.pos (b i) (b.ne_zero i)).1
    have hzero : ∀ β, ∑ a', qM (p i) (q i) (r i) (s i) β a' * b.repr (x a') i = 0 := fun β => by
      have h1 := congrFun hx (β, i)
      simpa [Φ] using h1
    have hf := qM_form (p i) (q i) (r i) (s i) (fun a' => b.repr (x a') i) (Pi.single a 1)
    simp only [hzero, zero_mul, Finset.sum_const_zero] at hf
    rw [← hsq i] at hf
    simp [Pi.single_apply] at hf
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact hf.resolve_left hN
  have hdim : finrank K (Fin 4 → V) = finrank K (Fin 4 × n → K) := by
    have e := ((LinearEquiv.piCongrRight fun _ : Fin 4 => b.equivFun).finrank_eq)
    rw [e]
    simp only [Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]
    first
      | (rw [Module.finrank_pi_fintype]; simp)
      | (rw [FiniteDimensional.finrank_pi_fintype]; simp)
      | simp [Module.finrank_pi_fintype]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun x y => ?_, fun x w => rfl⟩
  show ∑ w, Φ x w * c (Φ y w) = _
  have hc : ∀ (i : n) β, c (∑ a, qM (p i) (q i) (r i) (s i) β a * b.repr (y a) i) =
      ∑ a, qM (p i) (q i) (r i) (s i) β a * c (b.repr (y a) i) := by
    intro i β
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, qM_fix c (hp i) (hq i) (hr i) (hs i)]
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [hc]
  simp_rw [qM_form, ← hsq, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun a _ => H.form_repr b hb (x a) (y a)]
  exact Finset.sum_comm
end Herm4
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
