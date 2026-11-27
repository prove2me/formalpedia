-- Prove2me | solution 1 for EdgeDomSets.NPC.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:33:40.2967+00:00
-- url     : https://prove2.me/submissions/cf9510cf-d9a8-461b-836e-b2db2cdf3746

import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Supplement_TotalGraph
import Definitions.Def_GavrilSubtree_Chordal_Setting

set_option autoImplicit false

open EdgeDomSets
open EdgeDomSets.NPC
open EdgeDomSets.NPC.Supplement

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) :
    G.IsTree ↔ GavrilSubtree.Chordal.IsChordal (totalGraph G) := by
      classical
      have hTadj : ∀ x y, (totalGraph G).Adj x y ↔ totalAdj G x y := fun _ _ => Iff.rfl
      constructor
      · intro hTree
        obtain ⟨r⟩ := hG.nonempty
        obtain ⟨D, hD⟩ : ∃ D : V → ℕ, ∀ v, D v = G.dist r v := ⟨_, fun _ => rfl⟩
        have hP : ∀ v, ∃ p : G.Walk r v, p.IsPath ∧ p.length = D v := fun v => by
          obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist r v
          exact ⟨p, p.isPath_of_length_eq_dist hp, by rw [hD]; exact hp⟩
        have huniq : ∀ v (p q : G.Walk r v), p.IsPath → q.IsPath → p = q := fun v p q hp hq => by
          have := hTree.isAcyclic.path_unique ⟨p, hp⟩ ⟨q, hq⟩
          exact congrArg Subtype.val this
        have hle : ∀ v w, G.Adj v w → D w ≤ D v + 1 := fun v w h => by
          have h1 := hG.dist_triangle (u := r) (v := v) (w := w)
          have h2 : G.dist v w ≤ 1 := by simpa using SimpleGraph.dist_le h.toWalk
          rw [hD, hD]; omega
        have hne : ∀ v w, G.Adj v w → D v ≠ D w := fun v w h heq => by
          obtain ⟨pv, hpv, hlv⟩ := hP v
          obtain ⟨pw, hpw, hlw⟩ := hP w
          by_cases hw : w ∈ pv.support
          · have hlen : (pv.takeUntil w hw).length + (pv.dropUntil w hw).length = pv.length := by
              rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec]
            have hdrop : (pv.dropUntil w hw).length ≠ 0 := by
              intro h0
              exact h.ne (SimpleGraph.Walk.eq_of_length_eq_zero h0).symm
            have := SimpleGraph.dist_le (pv.takeUntil w hw)
            rw [← hD] at this; omega
          · have hpath : (pv.concat h).IsPath := by
              rw [← SimpleGraph.Walk.isPath_reverse_iff, SimpleGraph.Walk.reverse_concat, SimpleGraph.Walk.cons_isPath_iff]
              exact ⟨hpv.reverse, by simpa using hw⟩
            have := huniq w _ _ hpath hpw
            have hl := congrArg SimpleGraph.Walk.length this
            simp at hl; omega
        have hF1 : ∀ v w, G.Adj v w → D w = D v + 1 ∨ D v = D w + 1 := fun v w h => by
          have := hle v w h; have := hle w v h.symm; have := hne v w h; omega
        have hF2 : ∀ v w w', G.Adj w v → G.Adj w' v → D w + 1 = D v → D w' + 1 = D v → w = w' := by
          intro v w w' h h' hd hd'
          obtain ⟨pw, hpw, hlw⟩ := hP w
          obtain ⟨pw', hpw', hlw'⟩ := hP w'
          have e1 : (pw.concat h).IsPath :=
            SimpleGraph.Walk.isPath_of_length_eq_dist _ (by rw [SimpleGraph.Walk.length_concat, ← hD]; omega)
          have e2 : (pw'.concat h').IsPath :=
            SimpleGraph.Walk.isPath_of_length_eq_dist _ (by rw [SimpleGraph.Walk.length_concat, ← hD]; omega)
          have := huniq v _ _ e1 e2
          obtain ⟨hv, _⟩ := SimpleGraph.Walk.concat_inj this
          exact hv
        obtain ⟨dep, hdl, hdr⟩ : ∃ f : V ⊕ G.edgeSet → ℕ, (∀ v, f (Sum.inl v) = 2 * D v) ∧
            ∀ u w (h : s(u,w) ∈ G.edgeSet), f (Sum.inr ⟨s(u,w), h⟩) = D u + D w :=
          ⟨fun x => match x with
            | Sum.inl v => 2 * D v
            | Sum.inr e => Sym2.lift ⟨fun u w => D u + D w, fun u w => Nat.add_comm _ _⟩ e.1,
           fun v => rfl, fun u w h => rfl⟩
        have help1 : ∀ v a, (totalGraph G).Adj (Sum.inl v) a → dep a ≤ 2 * D v →
            ∃ w, ∃ hw : G.Adj v w, D w + 1 = D v ∧
              (a = Sum.inl w ∨ a = Sum.inr ⟨s(v,w), hw⟩) := by
          intro v a hva hdep
          rcases a with w | ⟨e, he⟩
          · rw [hdl] at hdep
            have hvw : G.Adj v w := hva
            refine ⟨w, hvw, ?_, Or.inl rfl⟩
            rcases hF1 v w hvw with h | h <;> omega
          · induction e using Sym2.ind with
            | h p q =>
              have hm : v ∈ s(p,q) := hva
              rw [Sym2.mem_iff] at hm
              have hpq : G.Adj p q := he
              rcases hm with rfl | rfl
              · rw [hdr] at hdep
                refine ⟨q, hpq, ?_, Or.inr rfl⟩
                rcases hF1 v q hpq with h | h <;> omega
              · rw [hdr] at hdep
                refine ⟨p, hpq.symm, ?_, Or.inr (by congr 2; exact Sym2.eq_swap)⟩
                rcases hF1 v p hpq.symm with h | h <;> omega
        have help2 : ∀ u w (h : s(u,w) ∈ G.edgeSet), D w = D u + 1 → ∀ a,
            (totalGraph G).Adj (Sum.inr ⟨s(u,w), h⟩) a → dep a ≤ D u + D w →
            (a = Sum.inl u ∨ ∃ f : G.edgeSet, a = Sum.inr f ∧ u ∈ f.1) := by
          intro u w h hduw a hadj hdep
          have huw : G.Adj u w := h
          rcases a with y | ⟨f, hf⟩
          · have hm : y ∈ s(u,w) := hadj
            rw [Sym2.mem_iff] at hm
            rcases hm with rfl | rfl
            · exact Or.inl rfl
            · rw [hdl] at hdep; omega
          · obtain ⟨hne', z, hz1, hz2⟩ := hadj
            rw [Sym2.mem_iff] at hz1
            rcases hz1 with rfl | rfl
            · exact Or.inr ⟨⟨f, hf⟩, rfl, hz2⟩
            · exfalso
              obtain ⟨t, rfl⟩ := Sym2.mem_iff_exists.mp hz2
              have hzt : G.Adj z t := hf
              rw [hdr] at hdep
              have hdt : D t + 1 = D z := by rcases hF1 z t hzt with h | h <;> omega
              have := hF2 z u t huw hzt.symm (by omega) hdt
              subst this
              exact hne' (by congr 1; exact Sym2.eq_swap)
        have help3 : ∀ u a b, a ≠ b → (a = Sum.inl u ∨ ∃ f : G.edgeSet, a = Sum.inr f ∧ u ∈ f.1) →
            (b = Sum.inl u ∨ ∃ f : G.edgeSet, b = Sum.inr f ∧ u ∈ f.1) → (totalGraph G).Adj a b := by
          intro u a b hab ha hb
          rcases ha with rfl | ⟨f, rfl, hf⟩ <;> rcases hb with rfl | ⟨g, rfl, hg⟩
          · exact absurd rfl hab
          · exact hg
          · exact hf
          · exact ⟨fun h => hab (by rw [h]), u, hf, hg⟩
        have key : ∀ x a b : V ⊕ G.edgeSet, (totalGraph G).Adj x a → (totalGraph G).Adj x b →
            a ≠ b → dep a ≤ dep x → dep b ≤ dep x → (totalGraph G).Adj a b := by
          intro x a b hxa hxb hab hda hdb
          rcases x with v | ⟨e, he⟩
          · rw [hdl] at hda hdb
            obtain ⟨w, hw, hdw, ha⟩ := help1 v a hxa hda
            obtain ⟨w', hw', hdw', hb⟩ := help1 v b hxb hdb
            have := hF2 v w w' hw.symm hw'.symm hdw hdw'
            subst this
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact absurd rfl hab
            · show w ∈ s(v,w); simp
            · show w ∈ s(v,w); simp
            · exact absurd rfl hab
          · induction e using Sym2.ind with
            | h p q =>
              have hpq : G.Adj p q := he
              rw [hdr] at hda hdb
              rcases hF1 p q hpq with h | h
              · exact help3 p a b hab (help2 p q he h a hxa hda) (help2 p q he h b hxb hdb)
              · have heq : (⟨s(p,q), he⟩ : G.edgeSet) = ⟨s(q,p), hpq.symm⟩ := by
                  congr 1; exact Sym2.eq_swap
                rw [heq] at hxa hxb
                exact help3 q a b hab (help2 q p _ h a hxa (by omega)) (help2 q p _ h b hxb (by omega))
        intro u c hc hlen
        obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image c.support.toFinset dep ⟨u, by simp⟩
        rw [List.mem_toFinset] at hx
        have hc1 : (c.rotate x hx).IsCycle := hc.rotate hx
        have hl1 : (c.rotate x hx).length = c.length := SimpleGraph.Walk.length_rotate c x hx
        have hedge : ∀ e, e ∈ (c.rotate x hx).edges ↔ e ∈ c.edges := fun e =>
          (SimpleGraph.Walk.rotate_edges c x hx).mem_iff
        obtain ⟨a, hxa, p, hcp⟩ : ∃ a, ∃ h : (totalGraph G).Adj x a, ∃ p : (totalGraph G).Walk a x,
            c.rotate x hx = SimpleGraph.Walk.cons h p := by
          cases hh : c.rotate x hx with
          | nil => rw [hh] at hl1; simp at hl1; omega
          | cons h' p => exact ⟨_, h', p, rfl⟩
        rw [hcp] at hc1 hl1 hedge
        rw [SimpleGraph.Walk.cons_isCycle_iff] at hc1
        obtain ⟨hp, hxap⟩ := hc1
        obtain ⟨b, hxb, q, hq⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hxa.ne p.reverse
        have hpr := hp.reverse
        rw [hq, SimpleGraph.Walk.cons_isPath_iff] at hpr
        obtain ⟨hqp, hxq⟩ := hpr
        have hlpq : p.length = q.length + 1 := by
          rw [← SimpleGraph.Walk.length_reverse p, hq, SimpleGraph.Walk.length_cons]
        have hpe : ∀ e, e ∈ p.edges ↔ e = s(x,b) ∨ e ∈ q.edges := fun e => by
          rw [← List.mem_reverse, ← SimpleGraph.Walk.edges_reverse, hq, SimpleGraph.Walk.edges_cons,
            List.mem_cons]
        simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.edges_cons, List.mem_cons] at hl1 hedge
        have hab : a ≠ b := by
          rintro rfl
          have := SimpleGraph.Walk.isPath_iff_eq_nil.mp hqp
          subst this
          simp at hlpq; omega
        obtain ⟨z, hbz, q', hq'⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hab.symm q
        have haS : a ∈ c.support := by
          have : s(x,a) ∈ c.edges := (hedge _).mp (Or.inl rfl)
          exact SimpleGraph.Walk.snd_mem_support_of_mem_edges _ this
        have hbS : b ∈ c.support := by
          have : s(x,b) ∈ c.edges := (hedge _).mp (Or.inr ((hpe _).mpr (Or.inl rfl)))
          exact SimpleGraph.Walk.snd_mem_support_of_mem_edges _ this
        refine ⟨a, haS, b, hbS, key x a b hxa hxb hab (hmax a (by simpa using haS))
          (hmax b (by simpa using hbS)), ?_⟩
        rw [← hedge]
        rintro (h | h)
        · rw [Sym2.eq_iff] at h
          rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hxa.ne h1.symm
          · exact hxb.ne h2.symm
        · rcases (hpe _).mp h with h | h
          · rw [Sym2.eq_iff] at h
            rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
            · exact hxa.ne h1.symm
            · exact hab h1
          · rw [hq'] at h hqp
            rw [SimpleGraph.Walk.cons_isPath_iff] at hqp
            rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at h
            rcases h with h | h
            · rw [Sym2.eq_iff] at h
              rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
              · exact hab h1
              · subst h1
                have := SimpleGraph.Walk.isPath_iff_eq_nil.mp hqp.1
                subst this
                rw [hq'] at hlpq
                simp at hlpq; omega
            · exact hqp.2 (SimpleGraph.Walk.snd_mem_support_of_mem_edges _ h)
      · intro hch
        rw [SimpleGraph.isTree_iff]
        refine ⟨hG, ?_⟩
        intro u0 c0 hc0
        have htri : ∀ a b d : V, G.Adj a b → G.Adj b d → G.Adj d a → False := by
          intro a b d hab hbd hda
          have h1 : (totalGraph G).Adj (Sum.inl a) (Sum.inl b) := hab
          have h2 : (totalGraph G).Adj (Sum.inl b) (Sum.inr ⟨s(b,d), hbd⟩) := (by simp : b ∈ s(b,d))
          have hne : (⟨s(b,d), hbd⟩ : G.edgeSet) ≠ ⟨s(d,a), hda⟩ := by
            intro h
            have := congrArg Subtype.val h
            simp only [Sym2.eq_iff] at this
            rcases this with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact hbd.ne h1
            · exact hab.ne h1.symm
          have h3 : (totalGraph G).Adj (Sum.inr ⟨s(b,d), hbd⟩) (Sum.inr ⟨s(d,a), hda⟩) :=
            ⟨hne, d, by simp, by simp⟩
          have h4 : (totalGraph G).Adj (Sum.inr ⟨s(d,a), hda⟩) (Sum.inl a) := (by simp : a ∈ s(d,a))
          have hab' := hab.ne
          have hbd' := hbd.ne
          have hda' := hda.ne
          have hne' : ∀ x, (⟨s(b,d), hbd⟩ : G.edgeSet) = x → x = ⟨s(d,a), hda⟩ → False :=
            fun x h h' => hne (h.trans h')
          have hw : (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h3
              (SimpleGraph.Walk.cons h4 SimpleGraph.Walk.nil)))).IsCycle := by
            simp [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.cons_isPath_iff, hab', hab'.symm,
              hne]
          obtain ⟨x, hx, y, hy, hxy, hnot⟩ := hch _ _ hw (by simp)
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hx hy
          simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
            List.not_mem_nil, or_false, not_or] at hnot
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl <;>
            first
            | exact hxy.ne rfl
            | exact hnot.1 rfl
            | exact hnot.2.1 rfl
            | exact hnot.2.2.1 rfl
            | exact hnot.2.2.2 rfl
            | exact hnot.1 Sym2.eq_swap
            | exact hnot.2.1 Sym2.eq_swap
            | exact hnot.2.2.1 Sym2.eq_swap
            | exact hnot.2.2.2 Sym2.eq_swap
            | (have hm : _ ∈ _ := hxy; simp at hm; tauto)
        have hlen1 : ∀ (y x : V) (q : G.Walk y x), q.length = 1 → s(y,x) ∈ q.edges := by
          intro y x q hq
          cases q with
          | nil => simp at hq
          | cons h q' =>
            cases q' with
            | nil => simp
            | cons h'' q'' => simp at hq
        have shortcut : ∀ (u x y : V) (c : G.Walk u u), c.IsCycle → x ∈ c.support → y ∈ c.support →
            G.Adj x y → s(x,y) ∉ c.edges →
            ∃ w, ∃ c' : G.Walk w w, c'.IsCycle ∧ c'.length < c.length := by
          intro u x y c hc hx hy hxy hnot
          have hc1 := hc.rotate hx
          have hl1 := SimpleGraph.Walk.length_rotate c x hx
          have hedge : ∀ e, e ∈ (c.rotate x hx).edges ↔ e ∈ c.edges := fun e =>
            (SimpleGraph.Walk.rotate_edges c x hx).mem_iff
          have hy1 : y ∈ (c.rotate x hx).support := (SimpleGraph.Walk.mem_support_rotate_iff c x hx).mpr hy
          have hp := hc1.isPath_takeUntil hy1
          have hlen : ((c.rotate x hx).takeUntil y hy1).length +
              ((c.rotate x hx).dropUntil y hy1).length = (c.rotate x hx).length := by
            rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec]
          have hpe := SimpleGraph.Walk.edges_takeUntil_subset (c.rotate x hx) hy1
          have hqe := SimpleGraph.Walk.edges_dropUntil_subset (c.rotate x hx) hy1
          have hq0 : ((c.rotate x hx).dropUntil y hy1).length ≠ 0 := by
            intro h0
            exact hxy.ne (SimpleGraph.Walk.eq_of_length_eq_zero h0).symm
          have hq1 : ((c.rotate x hx).dropUntil y hy1).length ≠ 1 := by
            intro h1
            have := hqe (hlen1 _ _ _ h1)
            rw [hedge, Sym2.eq_swap] at this
            exact hnot this
          refine ⟨y, SimpleGraph.Walk.cons hxy.symm ((c.rotate x hx).takeUntil y hy1), ?_, ?_⟩
          · rw [SimpleGraph.Walk.cons_isCycle_iff]
            refine ⟨hp, fun h => hnot ?_⟩
            have := hpe h
            rw [hedge, Sym2.eq_swap] at this
            exact this
          · rw [SimpleGraph.Walk.length_cons]; omega
        have hmain : ∀ (n : ℕ) (u : V) (c : G.Walk u u), c.IsCycle → c.length = n → False := by
          intro n
          induction n using Nat.strong_induction_on with
          | _ n ih =>
          intro u c hc hn
          by_cases h4 : 4 ≤ c.length
          · let φ : G →g totalGraph G := ⟨Sum.inl, fun h => h⟩
            have hinj : Function.Injective φ := Sum.inl_injective
            have hmc : (c.map φ).IsCycle := (SimpleGraph.Walk.map_isCycle_iff_of_injective hinj).mpr hc
            obtain ⟨x, hx, y, hy, hxy, hnot⟩ := hch _ _ hmc (by rw [SimpleGraph.Walk.length_map]; exact h4)
            rw [SimpleGraph.Walk.support_map, List.mem_map] at hx hy
            obtain ⟨x', hx', rfl⟩ := hx
            obtain ⟨y', hy', rfl⟩ := hy
            have hG' : G.Adj x' y' := hxy
            have hnot' : s(x',y') ∉ c.edges := fun h => hnot (by
              rw [SimpleGraph.Walk.edges_map]
              exact List.mem_map_of_mem (f := Sym2.map φ) h)
            obtain ⟨w, c', hc', hlen'⟩ := shortcut u x' y' c hc hx' hy' hG' hnot'
            exact ih _ (by omega) w c' hc' rfl
          · cases c with
            | nil => exact hc.not_nil SimpleGraph.Walk.Nil.nil
            | cons h1 c1 =>
              cases c1 with
              | nil => exact h1.ne rfl
              | cons h2 c2 =>
                cases c2 with
                | nil => simp [SimpleGraph.Walk.cons_isCycle_iff] at hc
                | cons h3 c3 =>
                  cases c3 with
                  | nil => exact htri _ _ _ h1 h2 h3
                  | cons h5 c5 => simp at h4
        exact hmain _ u0 c0 hc0 rfl
