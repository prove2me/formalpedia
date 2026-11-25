-- Prove2me | solution 1 for DetDLP.m89_s1_count_output_decode
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T21:25:28.296927+00:00
-- url     : https://prove2.me/submissions/bead1a82-5cc9-4323-adff-4761ba2b60ae

import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private noncomputable def evalZero (P : ℕ) : TruncPoly P 1 →+* ZMod (2 ^ P) :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom 0) (by
    have hI : Ideal.span {(Polynomial.X : Polynomial (ZMod (2^P)))^1} ≤
        RingHom.ker (Polynomial.evalRingHom (R := ZMod (2^P)) 0) := by
      apply Ideal.span_le.2
      intro x hx
      have hx' : x = Polynomial.X^1 := Set.mem_singleton_iff.mp hx
      subst x
      simp [RingHom.mem_ker]
    intro x hx
    exact RingHom.mem_ker.mp (hI hx))

private theorem truncPoly_one_eval (P : ℕ) (c : Fin 1 → ℕ)
    (hc : ∀ i, c i < 2 ^ P) :
    evalZero P (truncPolyOfCoeffs P 1 c) = c 0 := by
  rw [evalZero, truncPolyOfCoeffs]
  simp [Polynomial.evalRingHom, Polynomial.eval₂_monomial, Fin.sum_univ_one,
    ZMod.natCast_zmod_val, ZMod.val_natCast_of_lt (hc 0)]

theorem solution (P count : ℕ) (hcount : count < 2 ^ P)
    {w : List Bool} (hw : EncodesTruncPoly P 1 w
      (truncPolyOfCoeffs P 1 (fun _ => count))) :
    w = encodeNatListBin [count] := by
  rcases hw with ⟨c,hc,rfl,hval⟩
  have hcval := congrArg (evalZero P) hval
  rw [truncPoly_one_eval P c hc, truncPoly_one_eval P (fun _ => count) (fun _ => hcount)] at hcval
  have hcn : c 0 = count := by
    have hp := congrArg ZMod.val hcval
    rw [ZMod.val_natCast_of_lt (hc 0), ZMod.val_natCast_of_lt hcount] at hp
    exact hp.symm
  simp [hcn]

#print axioms solution
