-- Prove2me | solution 1 for DetDLP.d4b_outer_step_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T08:08:06.260394+00:00
-- url     : https://prove2.me/submissions/9a51f57b-05b5-4aca-950a-4241d6a4629d

import Definitions.Def_DetDLP_D4BOuterStep
import Theorems.Thm_DetDLP_f9a1_b_add_and_readout_poly
import Theorems.Thm_DetDLP_f9a2_b_mul_poly
import Theorems.Thm_DetDLP_f9a3_b_unpack_term_poly
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DetDLP.D4BOuter
open Groundwork Groundwork.PolyT D4BEntry D4Slice DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.map PolyT.flatMap PolyT.length PolyT.div PolyT.mod PolyT.mul PolyT.sum PolyT.idxOf
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_ite__226169acf219
  pair_poly field_poly listWord_poly nval_poly modBits_poly clipped_poly clog2_poly first_poly more_poly w5_M6Sort.cw_poly w5_M6Sort.encode_poly
variable {α : Type} [Enc α]
@[local fun_prop] private theorem decP {v : α → Bits} (hv : PolyT v) : PolyT fun x => w5_M6Sort.decode (v x) := w5_M6Sort.decode_poly.comp hv
@[local fun_prop] private theorem baP {v : α → Bits} (hv : PolyT v) : PolyT fun x => F9A1.bAddRaw (v x) := f9a1_b_add_and_readout_poly.2.2.1.comp hv
@[local fun_prop] private theorem rdP {v : α → Bits} (hv : PolyT v) : PolyT fun x => F9A1.bReadZeroDivRaw (v x) := f9a1_b_add_and_readout_poly.2.2.2.comp hv
@[local fun_prop] private theorem bmP {v : α → Bits} (hv : PolyT v) : PolyT fun x => F9A2.bMulRaw (v x) := f9a2_b_mul_poly.2.comp hv
@[local fun_prop] private theorem rawTermP {v : α → Bits} (hv : PolyT v) : PolyT fun x => ResidualScalarOracle.bUnpackTermRaw (v x) := f9a3_b_unpack_term_poly.2.2.comp hv
@[local fun_prop] private theorem rlP {v : α → List ℕ} (hv : PolyT v) : PolyT fun x => List.range (v x).length := by
  apply PolyT.range
  have h : PolyT fun x => (v x).map fun _ => () := by fun_prop
  exact h.congr (by simp)
@[local fun_prop] private theorem dispatchP {v0 : α → Bits} {v1 : α → ℕ} {v2 : α → Bits} (h0 : PolyT v0) (h1 : PolyT v1) (h2 : PolyT v2) :
    PolyT fun x => dispatch (v0 x) (v1 x) (v2 x) := by unfold dispatch; fun_prop
@[local fun_prop] private theorem rankP {v0 : α → Bits} {v1 : α → ℕ} (h0 : PolyT v0) (h1 : PolyT v1) :
    PolyT fun x => rank (v0 x) (v1 x) := by unfold rank; fun_prop
@[local fun_prop] private theorem headerCallP {v0 : α → Bits} {v1 : α → Bits} (h0 : PolyT v0) (h1 : PolyT v1) :
    PolyT fun x => headerCall (v0 x) (v1 x) := by unfold headerCall; fun_prop
@[local fun_prop] private theorem contextP {v0 : α → Bits} {v1 : α → Bits} {v2 : α → Bits} (h0 : PolyT v0) (h1 : PolyT v1) (h2 : PolyT v2) :
    PolyT fun x => context (v0 x) (v1 x) (v2 x) := by unfold context; fun_prop
@[local fun_prop] private theorem readOutP {v0 : α → Bits} {v1 : α → Bits} (h0 : PolyT v0) (h1 : PolyT v1) :
    PolyT fun x => readOut (v0 x) (v1 x) := by unfold readOut; fun_prop
@[local fun_prop] private theorem branchCallP {v0 : α → Bits} {v1 : α → Bits} {v2 : α → ℕ} (h0 : PolyT v0) (h1 : PolyT v1) (h2 : PolyT v2) :
    PolyT fun x => branchCall (v0 x) (v1 x) (v2 x) := by unfold branchCall; fun_prop
@[local fun_prop] private theorem afterHeaderP {v0 : α → Bits} {v1 : α → Bits} {v2 : α → Bits} (h0 : PolyT v0) (h1 : PolyT v1) (h2 : PolyT v2) :
    PolyT fun x => afterHeader (v0 x) (v1 x) (v2 x) := by unfold afterHeader; fun_prop
@[local fun_prop] private theorem sidesP {v0 : α → Bits} (h0 : PolyT v0) :
    PolyT fun x => sides (v0 x) := by unfold sides; fun_prop
@[local fun_prop] private theorem widthP {v0 : α → Bits} (h0 : PolyT v0) :
    PolyT fun x => width (v0 x) := by unfold width; fun_prop
@[local fun_prop] private theorem radixP {v0 : α → Bits} {v1 : α → Bits} (h0 : PolyT v0) (h1 : PolyT v1) :
    PolyT fun x => radix (v0 x) (v1 x) := by unfold radix; fun_prop
@[local fun_prop] private theorem spacesP {v0 : α → Bits} {v1 : α → Bits} (h0 : PolyT v0) (h1 : PolyT v1) :
    PolyT fun x => spaces (v0 x) (v1 x) := by unfold spaces; fun_prop
@[local fun_prop] private theorem digitCallP {v0 : α → Bits} {v1 : α → Bits} {v2 : α → ℕ} {v3 : α → Bits} {v4 : α → Bits} {v5 : α → Bits} (h0 : PolyT v0) (h1 : PolyT v1) (h2 : PolyT v2) (h3 : PolyT v3) (h4 : PolyT v4) (h5 : PolyT v5) :
    PolyT fun x => digitCall (v0 x) (v1 x) (v2 x) (v3 x) (v4 x) (v5 x) := by unfold digitCall; fun_prop
@[local fun_prop] private theorem afterBranchP {v0 : α → Bits} {v1 : α → Bits} {v2 : α → ℕ} {v3 : α → Bits} (h0 : PolyT v0) (h1 : PolyT v1) (h2 : PolyT v2) (h3 : PolyT v3) :
    PolyT fun x => afterBranch (v0 x) (v1 x) (v2 x) (v3 x) := by unfold afterBranch; fun_prop
@[local fun_prop] private theorem termP {v0 : α → Bits} {v1 : α → Bits} {v2 : α → List ℕ} {v3 : α → Bits} (h0 : PolyT v0) (h1 : PolyT v1) (h2 : PolyT v2) (h3 : PolyT v3) :
    PolyT fun x => term (v0 x) (v1 x) (v2 x) (v3 x) := by unfold term; fun_prop
@[local fun_prop] private theorem addP {v0 : α → Bits} {v1 : α → Bits} {v2 : α → Bits} (h0 : PolyT v0) (h1 : PolyT v1) (h2 : PolyT v2) :
    PolyT fun x => add (v0 x) (v1 x) (v2 x) := by unfold add; fun_prop
@[local fun_prop] private theorem mulP {v0 : α → Bits} {v1 : α → Bits} {v2 : α → Bits} (h0 : PolyT v0) (h1 : PolyT v1) (h2 : PolyT v2) :
    PolyT fun x => mul (v0 x) (v1 x) (v2 x) := by unfold mul; fun_prop
@[local fun_prop] private theorem nextAtP {v0 : α → List ℕ} {v1 : α → ℕ} (h0 : PolyT v0) (h1 : PolyT v1) :
    PolyT fun x => nextAt (v0 x) (v1 x) := by unfold nextAt; fun_prop
@[local fun_prop] private theorem advanceVecP {v0 : α → List ℕ} {v1 : α → ℕ} (h0 : PolyT v0) (h1 : PolyT v1) :
    PolyT fun x => advanceVec (v0 x) (v1 x) := by unfold advanceVec; fun_prop
@[local fun_prop] private theorem afterDigitP {v0 : α → Bits} {v1 : α → Bits} (h0 : PolyT v0) (h1 : PolyT v1) :
    PolyT fun x => afterDigit (v0 x) (v1 x) := by
  let ctx x := field 1 (v0 x); let acc x := field 2 (v0 x); let u x := nval 3 (v0 x)
  let br x := field 4 (v0 x); let a x := w5_M6Sort.decode (field 5 (v0 x))
  let ba x := add (ctx x) (field 6 (v0 x)) (term (ctx x) (br x) (a x) (v1 x))
  let i x := nextAt (a x) (radix (ctx x) (br x))
  let z x := add (ctx x) (acc x) (mul (ctx x) (field 1 (br x)) (ba x))
  have hc : PolyT ctx := field_poly 1 h0
  have hh : PolyT acc := field_poly 2 h0
  have hu : PolyT u := nval_poly 3 h0
  have hb : PolyT br := field_poly 4 h0
  have ha : PolyT a := decP (field_poly 5 h0)
  have hba : PolyT ba := addP hc (field_poly 6 h0) (termP hc hb ha h1)
  have hi : PolyT i := nextAtP ha (radixP hc hb)
  have hz : PolyT z := addP hc hh (mulP hc (field_poly 1 hb) hba)
  change PolyT fun x => if i x < (a x).length then digitCall (ctx x) (acc x) (u x) (br x) (advanceVec (a x) (i x)) (ba x) else if u x + 1 < nval 0 (field 1 (ctx x)) then branchCall (ctx x) (z x) (u x + 1) else readOut (ctx x) (z x)
  apply PolyT.ite'
  · fun_prop (disch := assumption)
  · exact digitCallP hc hh hu hb (advanceVecP ha hi) hba
  · apply PolyT.ite'
    · fun_prop (disch := assumption)
    · exact branchCallP hc hz (by fun_prop (disch := assumption))
    · exact readOutP hc hz
private theorem stepP (L₀ : ℕ) : PolyT (step L₀) := by unfold step; fun_prop
end DetDLP.D4BOuter

theorem solution : ∀ L₀ : ℕ, Groundwork.PolyT (DetDLP.outerStep L₀) := DetDLP.D4BOuter.stepP
