-- Prove2me | solution 1 for Formalism.GM.FockB.goodA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:47.840432+00:00
-- url     : https://prove2.me/submissions/8d7b7f2a-3807-441d-95e8-a5b6a6e3c0ab

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_letterAt_val
import Theorems.Thm_Formalism_GM_FockB_degU
import Theorems.Thm_Formalism_GM_FockB_finPos_val
import Theorems.Thm_Formalism_GM_FockB_chainEmb_inj
import Theorems.Thm_Formalism_GM_FockB_supp_Y
import Theorems.Thm_Formalism_GM_ProjS_eulL_of_support
import Theorems.Thm_Formalism_GM_ProjS_pderiv_of_free


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable {D : BlockData N}
namespace Formalism.GM.FockB
theorem _root_.solution [NeZero r] (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr) (g : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hg : g ∈ XiPolZ p N r D.T.t (D.B - jp)) (a : Option (Fin D.T.t)) :
    Good (wA D a) (eA D a) (zA D a) (sA D a) (oA D j jp a) (nA D j jp a)
      (rename (chainEmb N r D.T.t) y * g) := by
  have hyP : ∀ m ∈ y.support, ∀ b, ∑ c, m (b, c) = (D.lettersAt j jp).deg b := by
    have h := (Submodule.mem_inf.mp hy).1
    rw [Pol, mem_restrictSupport_iff] at h
    exact fun m hm => h hm
  have hgP : ∀ m ∈ g.support, (∀ v ∈ m.support, ∃ c, v = xiVar N r D.T.t c) ∧
      ∑ c, m (xiVar N r D.T.t c) = D.B - jp := by
    have h := (Submodule.mem_inf.mp hg).1
    rw [Submodule.restrictScalars_mem, mem_restrictSupport_iff] at h
    exact fun m hm => h hm
  have key : ∀ m ∈ (rename (chainEmb N r D.T.t) y * g).support, ∃ m1 ∈ y.support, ∃ m2 ∈ g.support,
      (∀ b c, m (chainEmb N r D.T.t (b, c)) = m1 (b, c)) ∧ (∀ c, m (xiVar N r D.T.t c) = m2 (xiVar N r D.T.t c)) ∧
      (∀ q, m (Sum.inr q) = 0) := by
    intro m hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := supp_Y y g m hm
    have hm2z : ∀ v, (∀ c, v ≠ xiVar N r D.T.t c) → m2 v = 0 := fun v hv => by
      by_contra h
      obtain ⟨c, hc⟩ := (hgP m2 hm2).1 v (Finsupp.mem_support_iff.mpr h)
      exact hv c hc
    refine ⟨m1, hm1, m2, hm2, ?_, ?_, ?_⟩
    · intro b c
      rw [Finsupp.add_apply, Finsupp.mapDomain_apply (chainEmb_inj _),
        hm2z (chainEmb N r D.T.t (b, c)) (fun c' h => (Fin.castSucc_lt_last b).ne
          (congrArg Prod.fst (Sum.inl_injective h : (Fin.castSucc b, c) = (Fin.last N, c')))), add_zero]
    · intro c
      rw [Finsupp.add_apply, Finsupp.mapDomain_notin_range, zero_add]
      rintro ⟨⟨b, c'⟩, h⟩
      exact (Fin.castSucc_lt_last b).ne
        (congrArg Prod.fst (Sum.inl_injective h : (Fin.castSucc b, c') = (Fin.last N, c)))
    · intro q
      rw [Finsupp.add_apply, Finsupp.mapDomain_notin_range, hm2z (Sum.inr q) (fun c h => by simp [xiVar] at h),
        add_zero]
      rintro ⟨x, h⟩
      simp [chainEmb] at h
  have hZS : ∀ q, pderiv (Sum.inr q) (rename (chainEmb N r D.T.t) y * g) = 0 := fun q =>
    ProjS.pderiv_of_free _ _ (fun m hm => by
      obtain ⟨_, _, _, _, _, _, h3⟩ := key m hm
      exact h3 q)
  have h2 := hB.2.2.2
  rcases a with _ | i
  · refine ⟨?_, ?_, hZS _, hZS _⟩
    · apply ProjS.eulL_of_support
      intro m hm
      obtain ⟨m1, hm1, m2, hm2, h1, -, -⟩ := key m hm
      show ∑ c, m (chainEmb N r D.T.t (D.uPos, c)) = _
      simp only [h1]
      rw [hyP m1 hm1, degU hB]
      rfl
    · apply ProjS.eulL_of_support
      intro m hm
      obtain ⟨m1, hm1, m2, hm2, -, h1, -⟩ := key m hm
      show ∑ c, m (xiVar N r D.T.t c) = _
      simp only [h1]
      rw [(hgP m2 hm2).2]
      rfl
  · have hi := hB.2.1 i
    have e0 : finPos N (D.T.pos i) = Fin.castSucc (D.letterAt (D.T.pos i)) := by
      apply Fin.ext
      rw [Fin.val_castSucc, letterAt_val (by omega), finPos_val (by omega)]
    have e1 : finPos N (D.T.pos i + 1) = Fin.castSucc (D.letterAt (D.T.pos i + 1)) := by
      apply Fin.ext
      rw [Fin.val_castSucc, letterAt_val (by omega), finPos_val (by omega)]
    refine ⟨?_, ?_, hZS _, hZS _⟩
    · apply ProjS.eulL_of_support
      intro m hm
      obtain ⟨m1, hm1, m2, hm2, h1, -, -⟩ := key m hm
      show ∑ c, m (Sum.inl (finPos N (D.T.pos i), c)) = _
      rw [e0]
      show ∑ c, m (chainEmb N r D.T.t (D.letterAt (D.T.pos i), c)) = _
      simp only [h1]
      rw [hyP m1 hm1]
      rfl
    · apply ProjS.eulL_of_support
      intro m hm
      obtain ⟨m1, hm1, m2, hm2, h1, -, -⟩ := key m hm
      show ∑ c, m (Sum.inl (finPos N (D.T.pos i + 1), c)) = _
      rw [e1]
      show ∑ c, m (chainEmb N r D.T.t (D.letterAt (D.T.pos i + 1), c)) = _
      simp only [h1]
      rw [hyP m1 hm1]
      rfl
end Formalism.GM.FockB
