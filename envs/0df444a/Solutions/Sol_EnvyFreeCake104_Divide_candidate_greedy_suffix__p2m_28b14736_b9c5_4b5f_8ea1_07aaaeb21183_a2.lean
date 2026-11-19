-- Prove2me | solution 1 for EnvyFreeCake104.Divide.candidate_greedy_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T18:36:55.616204+00:00
-- url     : https://prove2.me/submissions/3b42c07d-bc89-43fc-bf4f-633021fe5374

import Theorems.Thm_EnvyFreeCake104_Divide_trimAgainst_largest_admissible_suffix__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
import Theorems.Thm_EnvyFreeCake104_Divide_candidate_history_rule__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
import Definitions.Def_EnvyFreeCake104_Divide_Protocols

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hcut : ∀ (i : ι) (hi : i ∈ N) (Q : Piece) (hQ : Q.WF)
    (s : Rec ι) (hs : s.Valid V N) (hQs : s.Aligned Q)
    (w : ℝ) (hw : 0 ≤ w) (hwQ : w ≤ (V i).value Q.toSet)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
    ∃ (p : Pos) (s' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((prefixCut N i Q w).run s) tr₀ = some ((p, s'), tr) ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧
      (prefixList Q p).WF ∧ (suffixList Q p).WF ∧
      s'.Aligned (prefixList Q p) ∧ s'.Aligned (suffixList Q p) ∧
      (V i).value (prefixList Q p).toSet = w ∧
      (V i).value (suffixList Q p).toSet = (V i).value Q.toSet - w ∧
      IsSuffix (suffixList Q p).toSet Q ∧
      ∀ S : Set ℝ, IsSuffix S Q →
        (V i).value S ≤ (V i).value Q.toSet - w →
        S ⊆ (suffixList Q p).toSet)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (ag pc : List ι) (hag : ag.Nodup)
    (hmem : ∀ p ∈ ag.zip pc, p.1 ∈ N ∧ p.2 ∈ N) (o : ChoiceOracle ι) :
    ∃ (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (candidate N P ag pc) s = some ((Y, R), s', tr) ∧
      ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
        ag.zip pc = before ++ p :: after →
        ∀ S : Set ℝ, IsSuffix S (P p.2) →
          (∀ q ∈ before, (V q.1).value S ≤ (V q.1).value (Y q.1).toSet) →
          S ⊆ (Y p.1).toSet ∧
          ∀ i ∈ N, (V i).value S ≤ (V i).value (Y p.1).toSet := by
  let K : List ι → (ι → Piece) → Piece → Piece → Prop :=
    fun earlier Y Q B ↦ ∀ S : Set ℝ, IsSuffix S Q →
      (∀ i ∈ earlier, (V i).value S ≤ (V i).value (Y i).toSet) →
      S ⊆ B.toSet ∧ ∀ i ∈ N, (V i).value S ≤ (V i).value B.toSet
  have hstable : ∀ (earlier : List ι) (Y Z : ι → Piece) (Q B : Piece),
      (∀ i ∈ earlier, Y i = Z i) → K earlier Y Q B → K earlier Z Q B := by
    intro earlier Y Z Q B heq h S hS hb
    apply h S hS
    intro i hi
    rw [heq i hi]
    exact hb i hi
  have htrim : ∀ (Y : ι → Piece) (earlier : List ι) (Q : Piece) (st : Rec ι),
      (∀ i ∈ N, (Y i).WF) → (∀ i ∈ earlier, i ∈ N) →
      Q.WF → st.Valid V N →
      (∀ i ∈ N, st.Aligned (Y i)) → st.Aligned Q →
      ∀ (o' : ChoiceOracle ι) (tr₀ : List (Event ι)),
      ∃ (B rem : Piece) (st' : Rec ι) (tr : List (Event ι)),
        Prog.run V o' ((trimAgainst N Y earlier Q []).run st) tr₀ =
          some (((B, rem), st'), tr) ∧
        st'.Valid V N ∧ st.pts ⊆ st'.pts ∧ B.WF ∧ st'.Aligned B ∧ K earlier Y Q B := by
    intro Y earlier Q st hY hearlier hQ hst hYs hQs o' tr₀
    obtain ⟨B, rem, st', tr, hrun, hv, hp, hw, ha, _, _, hm⟩ :=
      EnvyFreeCake104.Divide.trimAgainst_largest_admissible_suffix__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
        V N hcut Y hY earlier hearlier Q [] hQ st hst hYs hQs o' tr₀
    exact ⟨B, rem, st', tr, hrun, hv, hp, hw, ha, hm⟩
  obtain ⟨Y, R, s', tr, hrun, hK⟩ :=
    EnvyFreeCake104.Divide.candidate_history_rule__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
      V N K hstable htrim P hP s hs hPs ag pc hag hmem o
  refine ⟨Y, R, s', tr, hrun, ?_⟩
  intro before p after he S hS hb
  apply hK before p after he S hS
  intro i hi
  obtain ⟨q, hq, hqi⟩ := List.mem_map.mp hi
  subst i
  exact hb q hq
