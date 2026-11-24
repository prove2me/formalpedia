-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.nFCaseA_of_lastVectorNotMemSup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:16.524649+00:00
-- url     : https://prove2.me/submissions/05327c45-e35c-4d50-9a96-ab4212be0de6

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_level_exists
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_level_lt_of_mem
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_finrank_compl
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_eq_of_levels
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_scalarUnique
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hasLevel_index_eq_of_mem_II

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hStep : Formalism.HermitianLatticeCounting.S6.NFStep) (hN0 : Formalism.HermitianLatticeCounting.S6.LastVectorNotMemSup) : Formalism.HermitianLatticeCounting.S6.NFCaseA := by
  intro K V _ _ _ _ _ H r F F' hμ hrel hm
  have key : ∀ x ∈ Formalism.HermitianLatticeCounting.S6.II F F', ∀ (a a' : Fin r) (al al' : K), F.HasLevel x a al →
      F'.HasLevel x a' al' → a = a' ∧
        F'.z - (al / al') • F.z ∈ F.X ⊔ F'.X ∧
        ∀ b : Fin r, a ≤ b → ∃ y ∈ Formalism.HermitianLatticeCounting.S6.II F F', F.HasLevel y b al ∧ F'.HasLevel y b al' :=
    fun x hx a a' al al' hF hF' => hasLevel_index_eq_of_mem_II F F' hStep hN0 hμ hrel
      (r - a.val - 1) x a a' al al' (by have := a.isLt; omega) hx hF hF'
  have hex : ∃ n : ℕ, ∃ x ∈ Formalism.HermitianLatticeCounting.S6.II F F', x ≠ 0 ∧ ∃ (a : Fin r) (al : K), a.val = n ∧ F.HasLevel x a al := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    obtain ⟨a, al, h⟩ := (level_exists F) (Submodule.mem_inf.1 hx).1 hx0
    exact ⟨a.val, x, hx, hx0, a, al, rfl, h⟩
  classical
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = Nat.find hex := ⟨_, rfl⟩
  have hspec := Nat.find_spec hex
  rw [← hjdef] at hspec
  obtain ⟨x₀, hx₀, hx₀0, a₀, al₀, ha₀, hF₀⟩ := hspec
  have hmin : ∀ x ∈ Formalism.HermitianLatticeCounting.S6.II F F', x ≠ 0 → ∀ (a : Fin r) (al : K), F.HasLevel x a al → j ≤ a.val := by
    intro x hx hx0 a al h
    rw [hjdef]
    exact Nat.find_min' hex ⟨x, hx, hx0, a, al, rfl, h⟩
  obtain ⟨a₀', al₀', hF₀'⟩ := (level_exists F') (Submodule.mem_inf.1 hx₀).2 hx₀0
  obtain ⟨-, hz, hall⟩ := key x₀ hx₀ a₀ a₀' al₀ al₀' hF₀ hF₀'
  obtain ⟨hal₀, -⟩ := id hF₀
  obtain ⟨hal₀', -⟩ := id hF₀'
  have hjr : j < r := by rw [← ha₀]; exact a₀.isLt
  have hlead : ∀ x ∈ Formalism.HermitianLatticeCounting.S6.II F F', x ≠ 0 → ∃ (a : Fin r) (al al' : K), F.HasLevel x a al ∧
      F'.HasLevel x a al' ∧ j ≤ a.val ∧ al = al₀ / al₀' * al' := by
    intro x hx hx0
    obtain ⟨a, al, hF⟩ := (level_exists F) (Submodule.mem_inf.1 hx).1 hx0
    obtain ⟨a', al', hF'⟩ := (level_exists F') (Submodule.mem_inf.1 hx).2 hx0
    obtain ⟨rfl, hz', -⟩ := key x hx a a' al al' hF hF'
    have hc := scalarUnique K V H r F F' _ _ hz' hz
    obtain ⟨hal', -⟩ := id hF'
    refine ⟨a, al, al', hF, hF', hmin x hx hx0 a al hF, ?_⟩
    rw [← hc]
    exact (div_mul_cancel₀ al hal').symm
  have hall' : ∀ a : Fin r, j ≤ a.val → ∃ x ∈ Formalism.HermitianLatticeCounting.S6.II F F', ∃ al al' : K,
      F.HasLevel x a al ∧ F'.HasLevel x a al' := by
    intro a ha
    obtain ⟨y, hy, h1, h2⟩ := hall a (Fin.le_iff_val_le_val.2 (by omega))
    exact ⟨y, hy, al₀, al₀', h1, h2⟩
  have hb : Formalism.HermitianLatticeCounting.S6.II F F' ⊓ F.Xa j = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyM, hyS⟩ := Submodule.mem_inf.1 hy
    rw [Submodule.mem_bot]
    by_contra hy0
    obtain ⟨a, al, hF⟩ := (level_exists F) (Submodule.mem_inf.1 hyM).1 hy0
    have h1 := (level_lt_of_mem F) hF hyS
    have h2 := hmin y hyM hy0 a al hF
    omega
  have hb' : Formalism.HermitianLatticeCounting.S6.II F F' ⊓ F'.Xa j = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyM, hyS⟩ := Submodule.mem_inf.1 hy
    rw [Submodule.mem_bot]
    by_contra hy0
    obtain ⟨a', al', hF'⟩ := (level_exists F') (Submodule.mem_inf.1 hyM).2 hy0
    obtain ⟨a, al, hF⟩ := (level_exists F) (Submodule.mem_inf.1 hyM).1 hy0
    obtain ⟨rfl, -, -⟩ := key y hyM a a' al al' hF hF'
    have h1 := (level_lt_of_mem F') hF' hyS
    have h2 := hmin y hyM hy0 a al hF
    omega
  have hI := (X_eq_of_levels F) j (Formalism.HermitianLatticeCounting.S6.II F F') inf_le_left (fun a ha => by
    obtain ⟨x, hx, al, al', h1, -⟩ := hall' a ha
    exact ⟨x, hx, al, h1⟩)
  have hI' := (X_eq_of_levels F') j (Formalism.HermitianLatticeCounting.S6.II F F') inf_le_right (fun a ha => by
    obtain ⟨x, hx, al, al', -, h2⟩ := hall' a ha
    exact ⟨x, hx, al', h2⟩)
  have hfin := (finrank_compl F) hjr.le (Formalism.HermitianLatticeCounting.S6.II F F') hI hb
  refine ⟨j, al₀ / al₀', hjr, ?_⟩
  unfold Formalism.HermitianLatticeCounting.S6.NFShape
  exact ⟨div_ne_zero hal₀ hal₀', hfin, hlead, hall', hb, hb', hI, hI', hz⟩
end Formalism.HermitianLatticeCounting.P
