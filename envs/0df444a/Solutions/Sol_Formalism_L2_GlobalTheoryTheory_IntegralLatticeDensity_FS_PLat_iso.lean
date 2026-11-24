-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.PLat.iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:28:04.670884+00:00
-- url     : https://prove2.me/submissions/1683669d-1826-4c7d-97da-d8cb5a9a8669

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_zero_left
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_PLat_basis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_qM_mem
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_coord
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_iso_of


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
variable {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {c : K →+* K} {h : V → V → K} {O : Subring K} {L : AddSubgroup V} {p : ℕ}
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
namespace PLat
theorem _root_.solution (P : PLat c h O L p) {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = finrank K V) :
    ∃ g : (Fin 4 → V) ≃ₗ[K] (Fin 4 × ι → K), (∀ x y, ∑ w, g x w * c (g y w) = ∑ a, h (x a) (y a)) ∧
      ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x : Fin 4 → V, (∀ a, x a ∈ L) → ∀ w, (s : K) * g x w ∈ O) ∧
        ∀ u : Fin 4 × ι → K, (∀ w, u w ∈ O) → ∀ a, (s : K) • g.symm u a ∈ L := by
  have H := P.herm
  obtain ⟨b, n, gL, gn, gp, go⟩ := P.basis hι
  choose a1 a2 a3 a4 h4 using fun i => Nat.sum_four_squares (n i)
  obtain ⟨g, hg, hform⟩ := H.iso_of b go (fun i => (a1 i : K)) (fun i => (a2 i : K)) (fun i => (a3 i : K))
    (fun i => (a4 i : K)) (fun i => map_natCast c _) (fun i => map_natCast c _) (fun i => map_natCast c _)
    (fun i => map_natCast c _) (fun i => by rw [gn i, ← h4 i]; push_cast; ring)
  have hn0 : ∀ i, (n i : K) ≠ 0 := by
    intro i e0
    have : n i = 0 := by exact_mod_cast e0
    exact gp i (this ▸ dvd_zero p)
  have hcop : Nat.Coprime (∏ j, n j) p :=
    Nat.Coprime.prod_left fun i _ => ((Nat.Prime.coprime_iff_not_dvd P.prime).2 (gp i)).symm
  have h1 : ∀ x : Fin 4 → V, (∀ a, x a ∈ L) → ∀ w, ((∏ j, n j : ℕ) : K) * g x w ∈ O := by
    intro x hx w
    rw [hform, Finset.mul_sum]
    refine O.sum_mem fun a _ => ?_
    have e : ((∏ j, n j : ℕ) : K) * b.repr (x a) w.2
        = ((∏ j ∈ Finset.univ.erase w.2, n j : ℕ) : K) * h (x a) (b w.2) := by
      rw [H.coord b go, gn, ← Finset.mul_prod_erase Finset.univ n (Finset.mem_univ w.2)]
      push_cast; ring
    have e' : ((∏ j, n j : ℕ) : K) * (qM (a1 w.2 : K) (a2 w.2 : K) (a3 w.2 : K) (a4 w.2 : K) w.1 a * b.repr (x a) w.2)
        = qM (a1 w.2 : K) (a2 w.2 : K) (a3 w.2 : K) (a4 w.2 : K) w.1 a *
          (((∏ j ∈ Finset.univ.erase w.2, n j : ℕ) : K) * h (x a) (b w.2)) := by
      rw [← e]; ring
    rw [e']
    exact O.mul_mem (qM_mem O (natCast_mem O _) (natCast_mem O _) (natCast_mem O _) (natCast_mem O _) _ _)
      (O.mul_mem (natCast_mem O _) (P.int _ (hx a) _ (gL _)))
  refine ⟨g, hg, ∏ j, n j, hcop, h1, ?_⟩
  intro u hu a
  refine P.unim _ fun y hy => ?_
  have e := hg (g.symm u) (Pi.single a y)
  rw [LinearEquiv.apply_symm_apply, Finset.sum_eq_single a] at e
  · rw [Pi.single_eq_same] at e
    rw [H.smul_left, ← e, Finset.mul_sum]
    refine O.sum_mem fun w _ => ?_
    have e2 : ((∏ j, n j : ℕ) : K) * (u w * c (g (Pi.single a y) w))
        = u w * c (((∏ j, n j : ℕ) : K) * g (Pi.single a y) w) := by
      rw [map_mul, map_natCast]; ring
    rw [e2]
    refine O.mul_mem (hu w) (P.cO _ (h1 _ ?_ w))
    intro a'
    by_cases ha : a' = a
    · subst ha; rwa [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne ha]; exact L.zero_mem
  · intro a' _ ha'
    rw [Pi.single_eq_of_ne ha', H.symm 0 _, H.zero_left, map_zero]
  · intro ha; exact absurd (Finset.mem_univ a) ha
end PLat
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
