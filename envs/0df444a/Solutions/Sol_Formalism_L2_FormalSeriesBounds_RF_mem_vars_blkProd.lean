-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.mem_vars_blkProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:49:06.173787+00:00
-- url     : https://prove2.me/submissions/78ee8482-1728-4175-8d05-be84c494c0f9

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {b : Fin n} {o : Orb} {w : WV (IIof r tau o)}
    (hx : ((b, ⟨o, w⟩) : Fin n × WVO (IIof r tau)) ∈ (blkProd X F n L pl).vars) :
    (b, w) ∈ (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o)).vars := by
  unfold blkProd at hx
  have h1 := MvPolynomial.vars_prod _ hx
  rw [Finset.mem_biUnion] at h1
  obtain ⟨o', -, h2⟩ := h1
  unfold toAll at h2
  have h3 := MvPolynomial.vars_rename _ _ h2
  rw [Finset.mem_image] at h3
  obtain ⟨y, hy, hyeq⟩ := h3
  simp only [Prod.mk.injEq] at hyeq
  obtain ⟨hy1, hy2⟩ := hyeq
  have ho : o' = o := congrArg Sigma.fst hy2
  subst ho
  have hw : y.2 = w := eq_of_heq (Sigma.mk.inj_iff.1 hy2).2
  rw [show (b, w) = y from Prod.ext hy1.symm hw.symm]
  exact hy
end Formalism.L2.FormalSeriesBounds.RF
