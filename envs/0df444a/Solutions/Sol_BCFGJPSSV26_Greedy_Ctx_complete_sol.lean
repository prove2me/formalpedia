-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Ctx.complete_sol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:59:06.451193+00:00
-- url     : https://prove2.me/submissions/c1e00b26-4183-41d1-a198-cafc67aebf64

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Bridge
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
import all Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_completeSeq_validSeq

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

namespace Ctx

variable (C : Ctx)

variable {C} {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)
include hX

section Iter

variable {b : Bool} {f θ : ℚ} {pre cur : List AAtom}

end Iter

/-- **CompleteSolution produces a solution** ([BCFGJPSSV26a, Observation D.8]): completing an
`η`-valid partial solution with atoms in range, for `f̂ ∈ (n η, 4 n M]`, gives an `η`-valid
solution. -/
theorem complete_sol {f η : ℚ} (hf : C.ip.n * C.ip.η < f) (hfM : f ≤ C.ip.fmax)
    (hη : 0 ≤ η) {H : List (List AAtom)} (hlen : H.length ≤ 2 * C.ip.R) (hok : C.SolOK H)
    (hv : EtaValid C.par X.d f η (decH hX H)) :
    Sol C.par X.d f η (decH hX (C.complete f H)) ∧ C.SolOK (C.complete f H) := by
  have hokG := C.complete_solOK f hok
  refine ⟨?_, hokG⟩
  have hGlen : (C.complete f H).length = 2 * C.ip.R := C.complete_length f hlen
  have hGapp := C.complete_eq_append f H
  have hdlen : (decH hX (C.complete f H)).length = 2 * C.par.R := by
    simp only [decH, List.length_map, hGlen]
    rfl
  refine sol_of_etaValid hX.good (M := C.ip.M) (fun j i ↦ X.d_nonneg j i) hX.dM hX.one_le_R
    ?_ ⟨0, hX.m_pos⟩ hdlen ?_ ?_
  · have := hX.θ_last
    exact le_trans (by linarith) this
  · intro p hp
    have hp' : p < 2 * C.ip.R := by rw [hdlen] at hp; exact hp
    by_cases hpH : p < H.length
    · have hpH' : p < (decH hX H).length := by simpa [decH] using hpH
      have e1 : (decH hX (C.complete f H)).take p = (decH hX H).take p := by
        rw [hGapp, decH, List.map_append, List.take_append_of_le_length (by simpa using hpH.le)]
        rfl
      have e2 : (decH hX (C.complete f H))[p] = (decH hX H)[p] := by
        have e : decH hX (C.complete f H) =
            decH hX H ++ decH hX ((C.complete f H).drop H.length) := by
          conv_lhs => rw [hGapp]
          exact List.map_append ..
        simp only [e]
        rw [List.getElem_append_left]
      rw [e1, e2]
      exact hv p hpH'
    · push Not at hpH
      have hgd := C.complete_getD f hpH hp'
      have hGp : (C.complete f H)[p]'(by omega) =
          C.completeSeq (typ1 p) f (C.θseq p) ((C.complete f H).take p).flatten [] := by
        rw [← hgd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        rfl
      have hokpre : ∀ a ∈ ((C.complete f H).take p).flatten ++ [], C.AtomOK a := by
        intro a ha
        rw [List.append_nil] at ha
        obtain ⟨S, hS, haS⟩ := List.mem_flatten.1 ha
        exact hokG a (List.mem_flatten.2 ⟨S, List.mem_of_mem_take hS, haS⟩)
      have h := completeSeq_validSeq hX hf hη (p := p) hokpre (fun t ht ↦ absurd ht (by simp))
      have e1 : ((decH hX (C.complete f H)).take p).flatten =
          decS hX ((C.complete f H).take p).flatten := by
        rw [← decH_flatten, decH, decH, List.map_take]
      have e2 : (decH hX (C.complete f H))[p] = decS hX (C.complete f H)[p] :=
        List.getElem_map ..
      rw [e1, e2, hGp]
      exact h
  · intro a ha
    rw [decH_flatten] at ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
    exact decA_wf hX (hokG a' ha')

end Ctx

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Ctx.complete_sol := @BCFGJPSSV26.Greedy.Ctx.complete_sol
