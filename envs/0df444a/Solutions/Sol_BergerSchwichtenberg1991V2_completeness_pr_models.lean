-- Prove2me | solution 1 for BergerSchwichtenberg1991V2.completeness_pr_models
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:58:25.971649+00:00
-- url     : https://prove2.me/submissions/f8e8fa93-f6ee-44e9-b76a-9a377fc760fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BergerSchwichtenberg1991V2_Models
import Theorems.Thm_BergerSchwichtenberg1991V2_lemma_3
import Theorems.Thm_BergerSchwichtenberg1991V2_theorem_1

set_option autoImplicit false

open BergerSchwichtenberg1991V2

universe u

theorem solution :
    (∃ N : EffectiveNumbering,
      ∀ (M : PRModel.{u}) (ρ : Ty),
        ∃ inv : M.Dom (.arr ρ .base),
          ∀ a : M.Dom ρ, M.IsLambdaDefinable ρ a →
            ∃ (t : Term) (ht : HasType t ρ),
              IsClosed t ∧ IsLongBetaNormal ρ t ∧
              M.eqM .base (M.appM inv a) (M.nu (N.natOfTerm t)) ∧
              ∀ η : M.Env, M.eqM ρ (M.eval ht η) a) ∧
    (∀ (M : PRModel.{u}) {ρ : Ty} {r s : Term} (hr : HasType r ρ) (hs : HasType s ρ),
      M.ModelsEq hr hs → BetaEtaEq r s) := by
  obtain ⟨N, hN⟩ := BergerSchwichtenberg1991V2.lemma_3
  constructor
  · refine ⟨N, fun M ρ => ?_⟩
    obtain ⟨A, hL, _, _, hcodeTerm, _⟩ := hN M
    rcases M with ⟨L, nu, nu_inj, reprBinary⟩
    rcases A with ⟨LA, tyF, tyIdx, codeTerm, codeIdx, append, mvar, appCode, abst, emb, funOp,
      extract, law_append, law_mvar, law_app, law_abst, law_code_inj, law_emb_congr, law_fun,
      law_extract⟩
    dsimp at hL
    subst hL
    let A' : AdmissibleModel.{u} :=
      { toLambdaModel := LA
        tyF := tyF
        tyIdx := tyIdx
        codeTerm := codeTerm
        codeIdx := codeIdx
        append := append
        mvar := mvar
        appCode := appCode
        abst := abst
        emb := emb
        funOp := funOp
        extract := extract
        law_append := law_append
        law_mvar := law_mvar
        law_app := law_app
        law_abst := law_abst
        law_code_inj := law_code_inj
        law_emb_congr := law_emb_congr
        law_fun := law_fun
        law_extract := law_extract }
    refine ⟨A'.inverse ρ, fun a ha => ?_⟩
    obtain ⟨t, ht, hpe, hclosed, hnorm, heval⟩ :=
      (BergerSchwichtenberg1991V2.theorem_1 A').1 ρ a ha
    have hcode_eq : codeTerm t = nu (N.natOfTerm t) := eq_of_heq (hcodeTerm t)
    have hinv_eq : LA.eqM .base (LA.appM (A'.inverse ρ) a) (nu (N.natOfTerm t)) := by
      have hsymm := LA.eqM_symm .base hpe.2
      change LA.eqM .base (LA.appM (A'.inverse ρ) a) (codeTerm t) at hsymm
      rwa [hcode_eq] at hsymm
    exact ⟨t, ht, hclosed, hnorm, hinv_eq, heval⟩
  · intro M ρ r s hr hs hmeq
    obtain ⟨A, hL, _⟩ := hN M
    rcases M with ⟨L, nu, nu_inj, reprBinary⟩
    rcases A with ⟨LA, tyF, tyIdx, codeTerm, codeIdx, append, mvar, appCode, abst, emb, funOp,
      extract, law_append, law_mvar, law_app, law_abst, law_code_inj, law_emb_congr, law_fun,
      law_extract⟩
    dsimp at hL
    subst hL
    let A' : AdmissibleModel.{u} :=
      { toLambdaModel := LA
        tyF := tyF
        tyIdx := tyIdx
        codeTerm := codeTerm
        codeIdx := codeIdx
        append := append
        mvar := mvar
        appCode := appCode
        abst := abst
        emb := emb
        funOp := funOp
        extract := extract
        law_append := law_append
        law_mvar := law_mvar
        law_app := law_app
        law_abst := law_abst
        law_code_inj := law_code_inj
        law_emb_congr := law_emb_congr
        law_fun := law_fun
        law_extract := law_extract }
    exact (BergerSchwichtenberg1991V2.theorem_1 A').2.2 hr hs hmeq
