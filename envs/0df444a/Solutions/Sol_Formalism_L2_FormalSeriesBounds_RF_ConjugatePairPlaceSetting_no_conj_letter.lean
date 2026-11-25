-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.ConjugatePairPlaceSetting.no_conj_letter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:20:10.491381+00:00
-- url     : https://prove2.me/submissions/997dd7da-d6b2-445a-abd4-4b7ea96b5aff

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_ConjugatePairPlaceSetting_no_conj
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
namespace ConjugatePairPlaceSetting
theorem _root_.solution (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (τ : T) (a1 : Fin (r τ)) (a2 : Fin (r (cc τ)))
    (b : Fin n)
    (h1 : (⟨τ, a1, b⟩ : Letter T r n) ∈ (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl)).vars)
    (h2 : (⟨cc τ, a2, b⟩ : Letter T r n) ∈ (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl)).vars) : False := by
  obtain ⟨x, hx, ex⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ h1)
  obtain ⟨x', hx', ex'⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ h2)
  obtain ⟨ρ, o, g, t, i⟩ := x
  obtain ⟨ρ', o', g', t', i'⟩ := x'
  have e1 : tau o g t = τ := congrArg Sigma.fst ex
  have e1' : tau o' g' t' = cc τ := congrArg Sigma.fst ex'
  have eρ : ρ = b := congrArg (fun ℓ : Letter T r n => ℓ.2.2) ex
  have eρ' : ρ' = b := congrArg (fun ℓ : Letter T r n => ℓ.2.2) ex'
  have e2 : tau o' g' t' = tau o (1 - g) t := by
    rw [e1', ← e1]
    have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · exact H.conj o t
    · exact H.conj' o t
  have e3 := H.inj (a₁ := (o', g', t')) (a₂ := (o, 1 - g, t)) e2
  simp only [Prod.mk.injEq] at e3
  obtain ⟨rfl, rfl, rfl⟩ := e3
  rw [eρ] at hx
  rw [eρ'] at hx'
  exact H.no_conj b o' g t' i i' hx hx'
end ConjugatePairPlaceSetting
end Formalism.L2.FormalSeriesBounds.RF
