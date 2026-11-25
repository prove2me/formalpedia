-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.block_membership_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:29:22.827098+00:00
-- url     : https://prove2.me/submissions/5f876f57-b911-4458-beec-9a5c288664c0

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksChart
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
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
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} (r : T → ℕ) (cc : T → T) (isX : T → Prop)
  (a : T → ℕ → ℕ) {Orb : Type} [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) (O : Subring C) (n : ℕ)
variable {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (h1 : NormOneHarmonic) (h2 : NormOneLineInvariant) (h3 : NormOneLineDegrees) (h4 : NormOneIntegral)
    (X : ∀ o, RowData C V d (IIof r tau o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)
    (inj : Function.Injective fun x : Orb × Fin 2 × ZMod d => tau x.1 x.2.1 x.2.2)
    (conj : ∀ o t, cc (tau o 0 t) = tau o 1 t) (conj' : ∀ o t, cc (tau o 1 t) = tau o 0 t)
    (hty : ∀ o g (x : IIof r tau o g), ((X o).G g).ty (Sum.inl x) = x.1)
    (std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val)
    (dich : ∀ o ∈ Z, (X o).Alt ∨ ∀ t, (X o).big 0 t) (hj : ∀ o ∈ Z, (X o).j' < (X o).n)
    (supp : ∀ o ∈ Z, ∀ g t k, ga o g t k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF g t) (tie : WtTie r tau Z ga a) :
    BlockMembership X n F (harmonicProductFamily r cc isX a tau O n) Z ga := by
  intro L off wt pl plinj
  have H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl := ⟨inj, conj, conj', hty, std, dich, hj, supp, off, wt, tie, plinj⟩
  exact ⟨⟨h1 C V d T r cc a Orb tau J X F Z ga n L pl H isX, h2 C V d T r cc a Orb tau J X F Z ga n L pl H,
    h3 C V d T r cc a Orb tau J X F Z ga n L pl H⟩, h4 C V d T r cc a Orb tau J X F Z ga n L pl H O⟩
end Formalism.L2.FormalSeriesBounds.RF
