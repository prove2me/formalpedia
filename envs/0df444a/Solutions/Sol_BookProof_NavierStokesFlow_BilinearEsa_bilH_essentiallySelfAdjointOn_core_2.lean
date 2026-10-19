-- Prove2me | solution 2 for BookProof.NavierStokesFlow.BilinearEsa.bilH_essentiallySelfAdjointOn_core
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:42:59.379489+00:00
-- url     : https://prove2.me/submissions/d62def99-c6f4-471a-9d98-d3c919a89d70

import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_relative_bound
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_commForm_bound
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_symmetricOn
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_deficiencyTrivialAt_bilH
-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.bilH_essentiallySelfAdjointOn_core
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.AffineFiber BookProof.NavierStokesFlow.IkebeKato
  BookProof.FarisLavine in
theorem h43_pairH_esa {ι : Type*} (P : PairShift ι) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((PairShift.pairH P).comp (Submodule.inclusion (finiteModes_le_maxDom P.sym))) :=
  essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds P.sym
    (fun k => le_trans zero_le_one (P.sym_ge_one k)) (PairShift.pairH P) 2 (32 * P.K ^ 2)
    (2 * P.step₁ * (1 / 4 + P.K) + 2 * P.step₂ * (1 / 4 + P.K))
    (PairShift.pairH_symmetricOn P)
    (by have := P.step₁_nonneg; have := P.step₂_nonneg; have := P.K_nonneg; positivity)
    (PairShift.pairH_relative_bound P) (PairShift.pairH_commForm_bound P)

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.AffineFiber BookProof.NavierStokesFlow.IkebeKato
  BookProof.NavierStokesFlow.HermiteFarisLavine BookProof.NavierStokesFlow.ShiftHamiltonian in
theorem h43_ns_eq {κ : ℝ} (hκ : 0 ≤ κ) :
    (nsH κ hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol κ)))
      = (affH hκ (le_refl (0:ℝ))).comp
          (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu κ 0)))) := by
  refine LinearMap.ext fun x => lp.ext (funext fun n => ?_)
  show hFun κ ((x : L2I ℕ) : ℕ → ℂ) n
    = (affData hκ (le_refl (0:ℝ))).fst.hFun ((x : L2I ℕ) : ℕ → ℂ) n
      + (affData hκ (le_refl (0:ℝ))).snd.hFun ((x : L2I ℕ) : ℕ → ℂ) n
  have hsh : ∀ m, shear 0 m = 0 := fun m => by simp [shear]
  have hsnd : (affData hκ (le_refl (0:ℝ))).snd.hFun ((x : L2I ℕ) : ℕ → ℂ) n = 0 := by
    simp only [ShiftData.hFun]
    have h1 : (affData hκ (le_refl (0:ℝ))).snd.hop (fun α =>
        (((affData hκ (le_refl (0:ℝ))).snd.amp α : ℝ) : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) α) n = 0 := by
      have : (fun α => (((affData hκ (le_refl (0:ℝ))).snd.amp α : ℝ) : ℂ)
          * ((x : L2I ℕ) : ℕ → ℂ) α) = 0 := by
        funext α
        show ((shear 0 α : ℝ) : ℂ) * _ = 0
        rw [hsh]; simp
      rw [this]
      by_cases hb : ∃ α, (affData hκ (le_refl (0:ℝ))).snd.shift α = n
      · obtain ⟨α, rfl⟩ := hb
        rw [ShiftData.hop_shift]; rfl
      · exact ShiftData.hop_eq_zero _ _ hb
    rw [h1, show (affData hκ (le_refl (0:ℝ))).amp₂ n = shear 0 n from rfl, hsh]
    simp
  rw [hsnd, add_zero]
  simp only [ShiftData.hFun, hFun]
  congr 1
  rw [show (affData hκ (le_refl (0:ℝ))).shift₁ n = n + 2 from rfl,
    show (affData hκ (le_refl (0:ℝ))).amp₁ n = amp κ n from rfl]
  congr 1
  rcases Nat.lt_or_ge n 2 with h | h
  · rw [show shift2 (fun n => (amp κ n : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) n) n = 0 by
      simp [shift2]; omega]
    symm
    apply ShiftData.hop_eq_zero
    rintro ⟨α, hα⟩
    have : α + 2 = n := hα
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [shift2_add_two (M := ℂ)]
    exact (ShiftData.hop_shift (M := ℂ) (affData hκ (le_refl (0:ℝ))).fst
      (fun α => (((affData hκ (le_refl (0:ℝ))).amp₁ α : ℝ) : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) α) m).symm

theorem solution (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) :
    EssentiallySelfAdjointOn (lpFiniteModes (ℕ × J)) (bilH κ) := by
  refine ⟨deficiencyTrivialAt_bilH κ hκ _ fun j => ?_, deficiencyTrivialAt_bilH κ hκ _ fun j => ?_⟩
  · rw [h43_ns_eq]; exact (h43_pairH_esa (BookProof.NavierStokesFlow.AffineFiber.affData (hκ j) (le_refl (0:ℝ)))).1
  · rw [h43_ns_eq]; exact (h43_pairH_esa (BookProof.NavierStokesFlow.AffineFiber.affData (hκ j) (le_refl (0:ℝ)))).2

