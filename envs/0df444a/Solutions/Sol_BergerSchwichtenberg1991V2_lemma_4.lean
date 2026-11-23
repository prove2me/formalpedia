-- Prove2me | solution 1 for BergerSchwichtenberg1991V2.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:57:34.981805+00:00
-- url     : https://prove2.me/submissions/69c7899e-ad6b-4b19-950b-d9d6652b18cd

import Definitions.Def_BergerSchwichtenberg1991V2_Models
import Theorems.Thm_BergerSchwichtenberg1991V2_lemma_2

set_option autoImplicit false

open BergerSchwichtenberg1991V2

universe u

private def shiftBinding (k : Index) : BindingTerm → BindingTerm
  | .free v => .free v
  | .bound ρ q => .bound ρ (k ++ q)
  | .app b₁ b₂ => .app (shiftBinding k b₁) (shiftBinding k b₂)
  | .lam ρ b => .lam ρ (shiftBinding k b)

private theorem binderPath_map_prefix (k : Index) (v : Var) :
    ∀ scope : List (Var × Index),
      binderPath v (scope.map (fun xq => (xq.1, k ++ xq.2))) =
        (binderPath v scope).map (k ++ ·)
  | [] => rfl
  | (x, q) :: scope => by
    simp only [List.map_cons, binderPath]
    by_cases hvx : v = x
    · simp [hvx]
    · simp [hvx, binderPath_map_prefix k v scope]

private theorem abstractBindings_shift (k : Index) :
    ∀ (t : Term) (scope : List (Var × Index)) (p : Index),
      abstractBindings (scope.map (fun xq => (xq.1, k ++ xq.2))) (k ++ p) t =
        shiftBinding k (abstractBindings scope p t)
  | .var v, scope, _ => by
    simp only [abstractBindings, binderPath_map_prefix]
    cases binderPath v scope <;> rfl
  | .app r s, scope, p => by
    simp only [abstractBindings, shiftBinding, List.append_assoc,
      abstractBindings_shift k r scope (p ++ zeroIdx),
      abstractBindings_shift k s scope (p ++ oneIdx)]
  | .lam x r, scope, p => by
    have hcons :
        (x, k ++ p) :: scope.map (fun xq => (xq.1, k ++ xq.2)) =
          ((x, p) :: scope).map (fun xq => (xq.1, k ++ xq.2)) := rfl
    simp only [abstractBindings, shiftBinding, List.append_assoc, hcons,
      abstractBindings_shift k r ((x, p) :: scope) (p ++ zeroIdx)]

private theorem alphaEq_app {r r' s s' : Term} (hr : AlphaEq r r') (hs : AlphaEq s s') :
    AlphaEq (.app r s) (.app r' s') := by
  unfold AlphaEq at *
  simp only [abstractBindings, List.nil_append]
  have h1 : abstractBindings ([] : List (Var × Index)) zeroIdx r =
      abstractBindings ([] : List (Var × Index)) zeroIdx r' := by
    have a1 := abstractBindings_shift zeroIdx r [] []
    have a2 := abstractBindings_shift zeroIdx r' [] []
    simp only [List.map_nil, List.append_nil] at a1 a2
    rw [a1, a2, hr]
  have h2 : abstractBindings ([] : List (Var × Index)) oneIdx s =
      abstractBindings ([] : List (Var × Index)) oneIdx s' := by
    have b1 := abstractBindings_shift oneIdx s [] []
    have b2 := abstractBindings_shift oneIdx s' [] []
    simp only [List.map_nil, List.append_nil] at b1 b2
    rw [b1, b2, hs]
  rw [h1, h2]

theorem solution (M : AdmissibleModel.{u}) :
    (∀ r : Term,
      M.eqM .base (M.f_extract (M.appM M.emb (M.codeTerm r)))
        (M.codeTerm (EXTRACT (EMB r)))) ∧
    (∀ r : Term,
      M.eqM M.tyF (M.appM M.emb (M.f_extract (M.appM M.emb (M.codeTerm r))))
        (M.appM M.emb (M.codeTerm r))) ∧
    (∀ r s : Term,
      M.eqM M.tyF
        (M.f_app (M.appM M.emb (M.codeTerm r)) (M.appM M.emb (M.codeTerm s)))
        (M.appM M.emb (M.codeTerm (.app r s)))) ∧
    (∀ (a : M.Dom (.arr M.tyIdx .base)) (r : Term),
      (∀ k : Index, M.eqM .base (M.appM a (M.codeIdx k)) (M.codeTerm (EMB r k))) →
      M.eqM M.tyF (M.fam a) (M.appM M.emb (M.codeTerm r))) := by
  have hL2 := BergerSchwichtenberg1991V2.lemma_2
  have h1 : ∀ r : Term,
      M.eqM .base (M.f_extract (M.appM M.emb (M.codeTerm r)))
        (M.codeTerm (EXTRACT (EMB r))) := by
    intro r
    exact M.law_extract (M.appM M.funOp (M.appM M.emb (M.codeTerm r))) r (M.law_fun r)
  have hemb_extract : ∀ r : Term, EMB (EXTRACT (EMB r)) = EMB r :=
    fun r => (hL2.1 (EXTRACT (EMB r)) r).mp (hL2.2.1 r)
  refine ⟨h1, ?_, ?_, ?_⟩
  · intro r
    exact M.eqM_trans _
      (M.appM_congr (M.eqM_refl _ M.emb) (h1 r))
      (M.law_emb_congr (EXTRACT (EMB r)) r (hemb_extract r))
  · intro r s
    unfold AdmissibleModel.f_app
    have happ_code :
        M.eqM .base
          (M.appM (M.appM M.appCode (M.f_extract (M.appM M.emb (M.codeTerm r))))
            (M.f_extract (M.appM M.emb (M.codeTerm s))))
          (M.codeTerm (.app (EXTRACT (EMB r)) (EXTRACT (EMB s)))) := by
      refine M.eqM_trans _ ?_ (M.law_app (EXTRACT (EMB r)) (EXTRACT (EMB s)))
      exact M.appM_congr
        (M.appM_congr (M.eqM_refl _ M.appCode) (h1 r))
        (h1 s)
    have halpha : AlphaEq (.app (EXTRACT (EMB r)) (EXTRACT (EMB s))) (.app r s) :=
      alphaEq_app (hL2.2.1 r) (hL2.2.1 s)
    have hemb_app : EMB (.app (EXTRACT (EMB r)) (EXTRACT (EMB s))) = EMB (.app r s) :=
      (hL2.1 _ _).mp halpha
    exact M.eqM_trans _
      (M.appM_congr (M.eqM_refl _ M.emb) happ_code)
      (M.law_emb_congr _ _ hemb_app)
  · intro a r ha
    unfold AdmissibleModel.fam
    exact M.eqM_trans _
      (M.appM_congr (M.eqM_refl _ M.emb) (M.law_extract a r ha))
      (M.law_emb_congr (EXTRACT (EMB r)) r (hemb_extract r))
