-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Ctx.MergeH.walkB_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:02:31.697206+00:00
-- url     : https://prove2.me/submissions/1177d350-f1ac-4971-a189-0dfaf3e41d85

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeWalk
import all Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeWalk
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_Hp_vs
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_VS_append_free
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_vs_completeSeq

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy.Ctx.MergeH

variable {C : Ctx}

variable {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

variable {p b : ℕ} {pre : List (List AAtom)} {Hp H'p : List AAtom}

section Hp

variable (hlen : pre.length = p) (hokp : C.SolOK pre)
  (hHp : Hp = C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten [])

include hX hokp hHp in
theorem Hp_length_le : Hp.length ≤ C.ip.m := by
  have h1 := (Hp_vs hX hokp hHp).nRegSeq_le hX (Hp_ok hHp)
  have h2 := length_eq_nReg_add_nFree Hp
  have h3 := nFreeSeqA_eq_zero fun a ha ↦ (Hp_new hHp a ha).1
  omega

end Hp

theorem dels_spec (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) (hokp : C.SolOK pre)
    {z : ℕ} {A : List AAtom} (hAreg : ∀ a ∈ A, a.2 = 0) :
    ∀ (D E : List AAtom) (pts : List (List AAtom × WKind)), (∀ a ∈ D, a.2 = 0) →
      (∀ a ∈ E, a.2 = 0) → WInv hX p b pre H'p pts →
      (∃ κ, pts.getLast? = some (A ++ D ++ (z, 1) :: E, κ)) →
      ∃ E' pts', (C.delStep p (C.fhat b) pre A.length)^[D.length]
          (A ++ D ++ (z, 1) :: E, pts) = (A ++ (z, 1) :: E', pts') ∧
        (∀ a ∈ E', a.2 = 0) ∧ WInv hX p b pre H'p pts' ∧
        ∃ κ, pts'.getLast? = some (A ++ (z, 1) :: E', κ)
  | [], E, pts, _, hE, hinv, hlast => ⟨E, pts, by simp, hE, hinv, by simpa using hlast⟩
  | d :: D, E, pts, hD, hE, hinv, ⟨κ, hlast⟩ => by
    have hd : d.2 = 0 := hD d (by simp)
    have hD' : ∀ a ∈ D, a.2 = 0 := fun a ha ↦ hD a (List.mem_cons_of_mem _ ha)
    rw [List.length_cons, Function.iterate_succ_apply]
    have hcur : A ++ d :: D ++ (z, 1) :: E = A ++ d :: (D ++ (z, 1) :: E) := by simp
    rw [hcur, delStep_eq]
    have hpt : WPt hX p b pre (A ++ d :: (D ++ (z, 1) :: E)) := by
      have := hinv.pt _ (List.mem_of_getLast? hlast)
      rwa [hcur] at this
    have hok1 : ∀ a ∈ A ++ (D ++ (z, 1) :: E), C.AtomOK a := fun a ha ↦ hpt.2.1 a (by
      simp only [List.mem_append, List.mem_cons] at ha ⊢
      tauto)
    -- the facts about the completion
    have hpref := List.prefix_iff_eq_append.1 (C.completeSeq_prefix (typ1 p) (C.fhat b)
      (C.θseq p) pre.flatten (A ++ (D ++ (z, 1) :: E)))
    rw [List.length_append] at hpref
    have hnew := C.completeSeq_new (typ1 p) (C.fhat b) (C.θseq p) pre.flatten
      (A ++ (D ++ (z, 1) :: E))
    rw [List.length_append] at hnew
    have hvsZ : VS hX p b pre (C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten
        (A ++ (D ++ (z, 1) :: E))) := by
      refine vs_completeSeq hX hokp ?_ hok1
      have h1 := hpt.1.1
      rw [show A ++ d :: (D ++ (z, 1) :: E) = A ++ [d] ++ (D ++ (z, 1) :: E) by simp,
        decS_append, decS_append] at h1
      rw [decS_append]
      exact AtomsValid.delete h1
    generalize C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten
      (A ++ (D ++ (z, 1) :: E)) = Zc at hpref hnew hvsZ ⊢
    generalize Zc.drop (A.length + (D ++ (z, 1) :: E).length) = Z at hpref hnew ⊢
    subst hpref
    have hokZ : ∀ a ∈ A ++ (D ++ (z, 1) :: E) ++ Z, C.AtomOK a := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hok1 a ha
      · exact ⟨(hnew a ha).2, by rw [(hnew a ha).1]; exact Nat.zero_le _⟩
    have hfreeY : nFreeSeqA (A ++ (D ++ (z, 1) :: E)) = 1 := by
      rw [nFreeSeqA_append, nFreeSeqA_append, nFreeSeqA_cons_free z 0,
        nFreeSeqA_eq_zero hAreg, nFreeSeqA_eq_zero hD', nFreeSeqA_eq_zero hE]
    have hfreeZ : nFreeSeqA (A ++ (D ++ (z, 1) :: E) ++ Z) = 1 := by
      rw [nFreeSeqA_append, hfreeY, nFreeSeqA_eq_zero fun a ha ↦ (hnew a ha).1]
    have hptZ : WPt hX p b pre (A ++ (D ++ (z, 1) :: E) ++ Z) := ⟨hvsZ, hokZ, hfreeZ.le⟩
    rw [List.take_of_length_le (hptZ.length_le hX)]
    have hinv' := hinv.snoc hX hlast (w := (A ++ (D ++ (z, 1) :: E) ++ Z,
      .removeComplete A d (D ++ (z, 1) :: E) Z)) ⟨by rw [hcur], rfl, hd,
        fun a ha ↦ (hnew a ha).1, hfreeY.le⟩ hptZ
    have hZc' : A ++ (D ++ (z, 1) :: E) ++ Z = A ++ D ++ (z, 1) :: (E ++ Z) := by simp
    rw [hZc'] at hinv' ⊢
    exact dels_spec hlen hv hokp hAreg D _ _ hD'
      (fun a ha ↦ by
        rcases List.mem_append.1 ha with ha | ha
        · exact hE a ha
        · exact (hnew a ha).1) hinv' ⟨.removeComplete A d (D ++ (z, 1) :: E) Z, by simp⟩

/-- **A round of the walk** keeps the invariant and makes the common prefix with `Hp` longer, or
`Hp` is already a prefix. -/
theorem round_spec (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) (hokp : C.SolOK pre)
    (hHp : Hp = C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten [])
    {st : List AAtom × List (List AAtom × WKind)} (hS : ∀ a ∈ st.1, a.2 = 0)
    (hinv : WInv hX p b pre H'p st.2) (hlast : ∃ κ, st.2.getLast? = some (st.1, κ)) :
    (∀ a ∈ (C.roundB p (C.fhat b) pre Hp st).1, a.2 = 0) ∧
      WInv hX p b pre H'p (C.roundB p (C.fhat b) pre Hp st).2 ∧
      (∃ κ, (C.roundB p (C.fhat b) pre Hp st).2.getLast? =
        some ((C.roundB p (C.fhat b) pre Hp st).1, κ)) ∧
      (Hp <+: (C.roundB p (C.fhat b) pre Hp st).1 ∨
        commonPrefixLen Hp st.1 < commonPrefixLen Hp (C.roundB p (C.fhat b) pre Hp st).1) := by
  obtain ⟨S, pts⟩ := st
  simp only at hS hinv hlast ⊢
  by_cases hpre : Hp <+: S
  · rw [roundB_of_prefix hpre]
    exact ⟨hS, hinv, hlast, .inl hpre⟩
  obtain ⟨κ, hlast⟩ := hlast
  have hqHp := cpl_lt_of_not_prefix hpre
  have hqS := cpl_le_right Hp S
  obtain ⟨q, hq⟩ : ∃ q, commonPrefixLen Hp S = q := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, (Hp.getD q (0, 0)).1 = z := ⟨_, rfl⟩
  rw [roundB_eq hpre hq hz]
  rw [hq] at hqHp hqS
  have hHpq : Hp[q] = (z, 0) := by
    rw [← hz, getD_of_lt hqHp]
    exact Prod.ext rfl (Hp_new hHp _ (List.getElem_mem hqHp)).1
  have hzm : z < C.ip.m := by
    have := (Hp_new hHp _ (List.getElem_mem hqHp)).2
    rwa [hHpq] at this
  obtain ⟨A, D, rfl, rfl⟩ : ∃ A D, S = A ++ D ∧ A.length = q :=
    ⟨S.take q, S.drop q, (List.take_append_drop q S).symm, by simp; omega⟩
  have hA : Hp.take A.length = A := by
    have := take_cpl Hp (A ++ D)
    rw [hq] at this
    simpa using this
  have hAreg : ∀ a ∈ A, a.2 = 0 := fun a ha ↦ hS a (List.mem_append_left _ ha)
  have hDreg : ∀ a ∈ D, a.2 = 0 := fun a ha ↦ hS a (List.mem_append_right _ ha)
  rw [show (A ++ D).length - A.length = D.length by simp]
  -- the first point: a free copy of `z` at offset `0`
  have hpt₀ := hinv.pt _ (List.mem_of_getLast? hlast)
  have hpt₁ : WPt hX p b pre (A ++ D ++ [(z, 1)]) := by
    refine ⟨hpt₀.1.append_free hX hlen hv z 0, fun a ha ↦ ?_, ?_⟩
    · rcases List.mem_append.1 ha with ha | ha
      · exact hpt₀.2.1 a ha
      · rw [List.mem_singleton.1 ha]
        exact ⟨hzm, Nat.le_add_left 1 _⟩
    · rw [nFreeSeqA_append, nFreeSeqA_eq_zero hS, nFreeSeqA_free z 0]
  have hinv₁ := hinv.snoc hX hlast (w := (A ++ D ++ [(z, 1)], .appendFree z)) ⟨rfl, hS⟩ hpt₁
  -- the deletions
  obtain ⟨E', pts', hit, hE', hinv', hlast'⟩ := dels_spec hX hlen hv hokp (H'p := H'p) (z := z)
    hAreg D [] _ hDreg (by simp) hinv₁ ⟨.appendFree z, by simp⟩
  rw [hit]
  simp only
  have hset : (A ++ (z, 1) :: E').set A.length (z, 0) = A ++ (z, 0) :: E' := by
    rw [List.set_append_right _ _ le_rfl]
    simp
  rw [hset]
  -- the last point: the free copy made regular
  obtain ⟨κ', hlast'⟩ := hlast'
  have hpt' := hinv'.pt _ (List.mem_of_getLast? hlast')
  have hreg₃ : ∀ a ∈ A ++ (z, 0) :: E', a.2 = 0 := by
    intro a ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with ha | rfl | ha
    · exact hAreg a ha
    · rfl
    · exact hE' a ha
  have hpt₃ : WPt hX p b pre (A ++ (z, 0) :: E') := by
    have hv₃ := (Hp_vs hX hokp hHp).1 A.length (by rw [decS_length]; omega)
    have hpairs : pairs (decS hX pre.flatten ++ decS hX (A ++ (z, 0) :: E')) =
        pairs (decS hX pre.flatten ++ decS hX (A ++ (z, 1) :: E')) := by
      rw [decS_append, decS_cons, decS_append, decS_cons, ← List.append_assoc,
        ← List.append_assoc]
      exact pairs_replace (decA_pair_one hX z).symm
    refine ⟨⟨?_, maximal_congr hpt'.1.2 hpairs⟩, fun a ha ↦ ?_, ?_⟩
    · have h1 := hpt'.1.1
      rw [decS_append, decS_cons] at h1 ⊢
      refine AtomsValid.replace h1 (decA_pair_one hX z).symm ?_
      rw [← decS_take, hA] at hv₃
      simp only [decS, List.getElem_map, hHpq] at hv₃
      exact hv₃
    · simp only [List.mem_append, List.mem_cons] at ha
      rcases ha with ha | rfl | ha
      · exact hpt'.2.1 a (by simp [ha])
      · exact ⟨hzm, Nat.zero_le _⟩
      · exact hpt'.2.1 a (by simp [ha])
    · rw [nFreeSeqA_eq_zero hreg₃]
      omega
  have hinv₃ := hinv'.snoc hX hlast' (w := (A ++ (z, 0) :: E', .toRegular))
    ⟨A, E', z, rfl, rfl⟩ hpt₃
  refine ⟨hreg₃, hinv₃, ⟨.toRegular, by simp⟩, .inr ?_⟩
  rw [hq]
  refine Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_cpl _ _ _ (by omega) (by simp) ?_)
  rw [List.take_add_one, List.getElem?_eq_getElem hqHp, hA, hHpq, List.take_append,
    List.take_of_length_le (by omega), show A.length + 1 - A.length = 1 by omega]
  simp

theorem rounds_spec (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) (hokp : C.SolOK pre)
    (hHp : Hp = C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten [])
    (hH'p : WPt hX p b pre H'p) (hreg : ∀ a ∈ H'p, a.2 = 0) : ∀ r : ℕ,
    (∀ a ∈ ((C.roundB p (C.fhat b) pre Hp)^[r] (H'p, [(H'p, .init)])).1, a.2 = 0) ∧
      WInv hX p b pre H'p ((C.roundB p (C.fhat b) pre Hp)^[r] (H'p, [(H'p, .init)])).2 ∧
      (∃ κ, ((C.roundB p (C.fhat b) pre Hp)^[r] (H'p, [(H'p, .init)])).2.getLast? =
        some (((C.roundB p (C.fhat b) pre Hp)^[r] (H'p, [(H'p, .init)])).1, κ)) ∧
      (Hp <+: ((C.roundB p (C.fhat b) pre Hp)^[r] (H'p, [(H'p, .init)])).1 ∨
        r ≤ commonPrefixLen Hp ((C.roundB p (C.fhat b) pre Hp)^[r] (H'p, [(H'p, .init)])).1)
  | 0 => by
    refine ⟨hreg, ⟨rfl, ?_, ?_⟩, ⟨.init, rfl⟩, .inr (Nat.zero_le _)⟩
    · intro w hw
      rw [List.mem_singleton.1 hw]
      exact hH'p
    · intro t ht
      simp at ht
  | r + 1 => by
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2, h3, h4⟩ := rounds_spec hlen hv hokp hHp hH'p hreg r
    obtain ⟨h5, h6, h7, h8⟩ := round_spec hX hlen hv hokp hHp h1 h2 h3
    refine ⟨h5, h6, h7, ?_⟩
    rcases h4 with h4 | h4
    · rw [roundB_of_prefix h4]
      exact .inl h4
    · rcases h8 with h8 | h8
      · exact .inl h8
      · exact .inr (by omega)

/-- **The walk of step B**: its points satisfy the invariant, and it ends with a sequence of
regular atoms with prefix `Hp`. -/
theorem walkB_spec (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) (hokp : C.SolOK pre)
    (hHp : Hp = C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten [])
    (hH'p : VS hX p b pre H'p) (hok : ∀ a ∈ H'p, C.AtomOK a) (hreg : ∀ a ∈ H'p, a.2 = 0) :
    WInv hX p b pre H'p (C.walkB p (C.fhat b) pre Hp H'p) ∧
      ∃ cur κ, (C.walkB p (C.fhat b) pre Hp H'p).getLast? = some (cur, κ) ∧ Hp <+: cur ∧
        ∀ a ∈ cur, a.2 = 0 := by
  have hpt : WPt hX p b pre H'p := ⟨hH'p, hok, by rw [nFreeSeqA_eq_zero hreg]; omega⟩
  obtain ⟨h1, h2, ⟨κ, h3⟩, h4⟩ := rounds_spec hX hlen hv hokp hHp hpt hreg C.ip.L
  refine ⟨h2, _, κ, h3, ?_, h1⟩
  rcases h4 with h4 | h4
  · exact h4
  · have h5 := cpl_le_left Hp ((C.roundB p (C.fhat b) pre Hp)^[C.ip.L] (H'p, [(H'p, .init)])).1
    have h6 := Hp_length_le hX hokp hHp
    have h7 := hX.L_ge
    omega

end BCFGJPSSV26.Greedy.Ctx.MergeH

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Ctx.MergeH.walkB_spec := @BCFGJPSSV26.Greedy.Ctx.MergeH.walkB_spec
