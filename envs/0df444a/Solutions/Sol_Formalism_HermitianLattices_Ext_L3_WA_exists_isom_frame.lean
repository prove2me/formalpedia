-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.exists_isom_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:59:19.832841+00:00
-- url     : https://prove2.me/submissions/9a44bb36-c7c4-480d-9f42-f2473123adef

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_exists_next
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_exists_isom_fix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.WA
theorem _root_.solution (hS : IsHermSemilocal S) (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0)
    (hM : IsSelfDualMod S h M) {n : ℕ} (e : Fin n → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i, g (e i) ∈ M := by
  have hsym : ∀ u w : V, star (h u w) = h w u := by
    intro u w
    have hsu := hs.eq u w
    rwa [starRingEnd_apply] at hsu
  have key : ∀ k : ℕ, k ≤ n → ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i : Fin n, (i : ℕ) < k → g (e i) ∈ M := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, (Formalism.HermitianLatticesTheory.isom h).one_mem, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨g, hg, hgM⟩ := ih (Nat.le_of_succ_le hk)
      have hgi : ∀ u w : V, h (g u) (g w) = h u w := hg
      obtain ⟨kk, hkk⟩ : ∃ kk : Fin n, (kk : ℕ) = k := ⟨⟨k, Nat.lt_of_succ_le hk⟩, rfl⟩
      have hxx : ∀ i j : Fin n, h (g (e i)) (g (e j)) = if i = j then 1 else 0 := by
        intro i j
        rw [hgi, he]
      obtain ⟨z, hzM, hzz, hzo⟩ := exists_next hS hs hM (fun i => g (e i)) hxx
        (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k))
        (fun i hi => hgM i (Finset.mem_filter.1 hi).2) kk (by simp [hkk])
      have hzo' : ∀ i : Fin n, (i : ℕ) < k → h (g (e i)) z = 0 := fun i hi =>
        hzo i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      have hk1 : h (g (e kk)) (g (e kk)) = 1 := by
        rw [hxx]
        simp
      obtain ⟨τ, hτ, hτk, hτfix⟩ := exists_isom_fix hs hd hk1 hzz
      refine ⟨τ * g, (Formalism.HermitianLatticesTheory.isom h).mul_mem hτ hg, ?_⟩
      intro i hi
      show τ (g (e i)) ∈ M
      rcases Nat.lt_or_ge (i : ℕ) k with hlt | hge
      · have h1 : h (g (e kk)) (g (e i)) = 0 := by
          rw [hxx]
          have hne : kk ≠ i := by
            intro h'
            rw [← h', hkk] at hlt
            exact lt_irrefl _ hlt
          simp [hne]
        have h2 : h z (g (e i)) = 0 := by
          rw [← hsym, hzo' i hlt, star_zero]
        rw [hτfix _ h1 h2]
        exact hgM i hlt
      · have hik : i = kk := Fin.ext (by omega)
        rw [hik, hτk]
        exact hzM
  obtain ⟨g, hg, hgM⟩ := key n le_rfl
  exact ⟨g, hg, fun i => hgM i i.isLt⟩
end Formalism.HermitianLattices.Ext.L3.WA
