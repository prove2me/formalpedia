-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_fin_filter_mod_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:25:03.855861+00:00
-- url     : https://prove2.me/submissions/6adf1267-b644-4094-bab0-d842f7b4c4fd

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {blocks q : ℕ} (hq : 0 < q) (S : Finset (Fin q)) :
    (Finset.univ.filter
      (fun x : Fin (blocks * q) =>
        (⟨(x : ℕ) % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card =
      blocks * S.card := by
  classical
  let e : Fin blocks × Fin q ≃ Fin (blocks * q) :=
    finProdFinEquiv
  have hres (x : Fin (blocks * q)) :
      (⟨(x : ℕ) % q, Nat.mod_lt _ hq⟩ : Fin q) = (e.symm x).2 := by
    apply Fin.ext
    simp [e, finProdFinEquiv]
  calc
    (Finset.univ.filter
      (fun x : Fin (blocks * q) =>
        (⟨(x : ℕ) % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card =
        ((Finset.univ : Finset (Fin blocks)) ×ˢ S).card := by
          apply Finset.card_bij (fun x _ => e.symm x)
          · intro x hx
            have hxS := (Finset.mem_filter.mp hx).2
            simp only [Finset.mem_product, Finset.mem_univ, true_and]
            rw [← hres x]
            exact hxS
          · intro x _ y _ hxy
            exact e.symm.injective hxy
          · intro y hy
            refine ⟨e y, ?_, e.symm_apply_apply y⟩
            have hyS : y.2 ∈ S := (Finset.mem_product.mp hy).2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hres (e y), e.symm_apply_apply]
            exact hyS
    _ = blocks * S.card := by simp
end CollatzEndpointTransport.Terras
