-- Prove2me | solution 1 for BudgetAgg.NashChar.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:23.652279+00:00
-- url     : https://prove2.me/submissions/ade32b5e-b889-4215-a594-fa96f0b626a6

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_LpModel

open BudgetAgg
open BudgetAgg.NashChar
open BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Theorem 2, p. 15: with `ℓ∞` preferences, `m ≥ 3`, `n ≥ 3`, no mechanism is
efficient, strategyproof and proportional. -/
theorem solution {n m : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) (f : Mechanism n m) :
    ¬ (IsEfficientMech lInfUtil f ∧ IsStrategyproofFor lInfUtil f ∧ IsProportional f) := by
      classical
      intro H
      rcases H with ⟨he, hs, hp⟩
      let d := fun (p q : stdSimplex ℝ (Fin m)) => -lInfUtil p q
      have dle (p q : stdSimplex ℝ (Fin m)) (x : ℝ) :
          d p q ≤ x ↔ ∀ j, |p.val j - q.val j| ≤ x := by
        simp [d, lInfUtil, Finset.sup'_le_iff]
      have dc (p q : stdSimplex ℝ (Fin m)) (j : Fin m) :
          |p.val j - q.val j| ≤ d p q := (dle p q _).mp le_rfl j
      have qle (q : stdSimplex ℝ (Fin m)) (j : Fin m) : q.val j ≤ 1 := by
        simpa [q.property.2] using Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => q.property.1 k) (Finset.mem_univ j)
      have pair (q : stdSimplex ℝ (Fin m)) (a b : Fin m) (hab : a ≠ b) :
          q.val a + q.val b ≤ 1 := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (show ({a,b} : Finset (Fin m)) ⊆ Finset.univ by simp)
          (fun j _ _ => q.property.1 j)
        simpa [Finset.sum_pair hab, q.property.2] using this
      have triple (q : stdSimplex ℝ (Fin m)) (a b c : Fin m)
          (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
          q.val a + q.val b + q.val c ≤ 1 := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (show ({a,b,c} : Finset (Fin m)) ⊆ Finset.univ by simp)
          (fun j _ _ => q.property.1 j)
        simpa [Finset.sum_insert, hab, hac, hbc, q.property.2, add_assoc] using this
      let pure (a : Fin m) : stdSimplex ℝ (Fin m) :=
        ⟨fun j => if j = a then 1 else 0, by
          constructor
          · intro j; dsimp; split_ifs <;> norm_num
          · simp⟩
      have pure_d (a : Fin m) (q : stdSimplex ℝ (Fin m)) : d (pure a) q = 1-q.val a := by
        apply le_antisymm
        · apply (dle _ _ _).mpr
          intro j
          by_cases hj : j = a
          · subst j; simpa [pure, abs_of_nonneg (sub_nonneg.mpr (qle q a))]
          · simp only [pure, if_neg hj, zero_sub, abs_neg, abs_of_nonneg (q.property.1 j)]
            linarith [pair q j a hj]
        · have := dc (pure a) q a
          simpa [pure, abs_of_nonneg (sub_nonneg.mpr (qle q a))] using this
      let tri (a b c : Fin m) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
          (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hxyz : x+y+z=1) : stdSimplex ℝ (Fin m) :=
        ⟨fun j => (if j=a then x else 0) + (if j=b then y else 0) + (if j=c then z else 0), by
          constructor
          · intro j; dsimp; split_ifs <;> linarith
          · simpa [Finset.sum_add_distrib] using hxyz⟩
      let mix (a b : Fin m) (hab : a ≠ b) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) : stdSimplex ℝ (Fin m) :=
        ⟨fun j => (if j=a then t else 0) + (if j=b then 1-t else 0), by
          constructor
          · intro j; dsimp; split_ifs <;> linarith
          · simp [Finset.sum_add_distrib]⟩
      have sp (i : Fin n) (P P' : Profile n m) (h : ∀ j, j ≠ i → P' j = P j) :
          d (P i) (f P) ≤ d (P i) (f P') := neg_le_neg (hs i P P' h)
      have structure_claim (a b c : Fin m) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
          (u v w : Fin n) (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v)
          (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
          let P : Profile n m := fun i => if i=u then mix a b hab t ht ht1 else if i=v then pure c else pure b
          let q := f P
          q.val a + q.val b + q.val c = 1 ∧ (q.val c ≤ t → 1-t ≤ q.val b) := by
        dsimp only
        let P : Profile n m := fun i => if i=u then mix a b hab t ht ht1 else if i=v then pure c else pure b
        let q := f P
        let p := mix a b hab t ht ht1
        have improve (q' : stdSimplex ℝ (Fin m)) (hc : q'.val c = q.val c)
            (hb : q.val b < q'.val b) (hd : d p q' ≤ d p q) : False := by
          apply he P
          refine ⟨q', ?_, w, ?_⟩
          · intro i
            change lInfUtil (P i) q ≤ lInfUtil (P i) q'
            by_cases hi : i=u
            · subst i
              have hh : P u = p := by simp [P, p]
              rw [hh]
              dsimp [d] at hd
              linarith
            · by_cases hiv : i=v
              · have hh : P i = pure c := by simp [P, hi, hiv, Ne.symm huv]
                rw [hh]
                have h1 := pure_d c q
                have h2 := pure_d c q'
                dsimp [d] at h1 h2
                rw [hc] at h2
                linarith
              · have hh : P i = pure b := by simp [P, hi, hiv, Ne.symm huv]
                rw [hh]
                have h1 := pure_d b q
                have h2 := pure_d b q'
                dsimp [d] at h1 h2
                linarith
          · have hh : P w = pure b := by simp [P, hwu, hwv]
            rw [hh]
            have h1 := pure_d b q
            have h2 := pure_d b q'
            dsimp [d] at h1 h2
            linarith
        have ca := dc p q a
        have cb := dc p q b
        have cc := dc p q c
        simp [p, mix, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc] at ca cb cc
        have ha := (abs_le.mp ca)
        have hb := (abs_le.mp cb)
        have hc := (abs_le.mp cc)
        have hd0 : 0 ≤ d p q := le_trans (abs_nonneg _) ca
        have hsum : q.val a + q.val b + q.val c = 1 := by
          apply le_antisymm (triple q a b c hab hac hbc)
          by_contra hh
          have hlt : q.val a + q.val b + q.val c < 1 := lt_of_not_ge hh
          let q' := tri a b c hab hac hbc (q.val a) (1-q.val a-q.val c) (q.val c)
            (q.property.1 a) (by linarith [pair q a c hac]) (q.property.1 c) (by ring)
          apply improve q' (by simp [q', tri, Ne.symm hac, Ne.symm hbc])
            (by dsimp [q', tri]; simp [Ne.symm hab, hbc]; linarith)
          apply (dle _ _ _).mpr
          intro j
          by_cases hja : j=a
          · subst j; simpa [q', tri, p, mix, hab, hac] using ca
          · by_cases hjb : j=b
            · subst j
              simp [q', tri, p, mix, Ne.symm hab, hbc]
              apply abs_le.mpr
              constructor <;> linarith [q.property.1 c]
            · by_cases hjc : j=c
              · subst j; simpa [q', tri, p, mix, Ne.symm hac, Ne.symm hbc] using cc
              · simpa [q', tri, p, mix, hja, hjb, hjc] using hd0
        refine ⟨hsum, ?_⟩
        intro hct
        by_contra hh
        have hlt : q.val b < 1-t := lt_of_not_ge hh
        let q' := tri a b c hab hac hbc (t-q.val c) (1-t) (q.val c)
          (by linarith) (by linarith) (q.property.1 c) (by ring)
        apply improve q' (by simp [q', tri, Ne.symm hac, Ne.symm hbc])
          (by simpa [q', tri, Ne.symm hab, hbc] using hlt)
        apply (dle _ _ _).mpr
        intro j
        by_cases hja : j=a
        · subst j
          simp [q', tri, p, mix, hab, hac, abs_of_nonneg (q.property.1 c)]
          linarith
        · by_cases hjb : j=b
          · subst j; simpa [q', tri, p, mix, Ne.symm hab, hbc] using hd0
          · by_cases hjc : j=c
            · subst j; simpa [q', tri, p, mix, Ne.symm hac, Ne.symm hbc] using cc
            · simpa [q', tri, p, mix, hja, hjb, hjc] using hd0
      have dlt (p q : stdSimplex ℝ (Fin m)) (x : ℝ) :
          d p q < x ↔ ∀ j, |p.val j - q.val j| < x := by
        simp [d, lInfUtil, Finset.sup'_lt_iff]
      have zero_other (q : stdSimplex ℝ (Fin m)) (a b c : Fin m)
          (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
          (h : q.val a+q.val b+q.val c=1) (j : Fin m)
          (hja : j ≠ a) (hjb : j ≠ b) (hjc : j ≠ c) : q.val j = 0 := by
        have hh := Finset.sum_le_sum_of_subset_of_nonneg
          (show ({j,a,b,c} : Finset (Fin m)) ⊆ Finset.univ by simp)
          (fun k _ _ => q.property.1 k)
        simp [Finset.sum_insert, hja, hjb, hjc, hab, hac, hbc, q.property.2] at hh
        linarith [q.property.1 j]
      let r : ℝ := 1/(n:ℝ)
      have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
      have hr : 0 < r := by dsimp [r]; positivity
      have hr3 : 3*r ≤ 1 := by
        dsimp [r]
        rw [← mul_div_assoc, mul_one]
        apply (div_le_iff₀ hn0).mpr
        simpa using (show (3:ℝ) ≤ n by exact_mod_cast hn)
      have base (u v : Fin n) (huv : u ≠ v) (a b c : Fin m) :
          let B : Profile n m := fun i => if i=u then pure a else if i=v then pure c else pure b
          ∀ j, (f B).val j = r*(pure a).val j + (1-2*r)*(pure b).val j + r*(pure c).val j := by
        dsimp only
        let B : Profile n m := fun i => if i=u then pure a else if i=v then pure c else pure b
        have hsingle : IsSingleMinded B := by
          intro i j
          have ps (k : Fin m) : (pure k).val j = 0 ∨ (pure k).val j = 1 := by
            by_cases hj : j=k <;> simp [pure, hj]
          by_cases hi : i=u
          · simpa [B, hi] using ps a
          · by_cases hiv : i=v
            · simpa [B, hi, hiv, Ne.symm huv] using ps c
            · simpa [B, hi, hiv] using ps b
        intro j
        have hb := hp B hsingle j
        have hh : (∑ i, (B i).val j) = (n:ℝ)*(pure b).val j +
            ((pure a).val j-(pure b).val j) + ((pure c).val j-(pure b).val j) := by
          calc
            _ = ∑ i : Fin n, ((pure b).val j +
                (if i=u then (pure a).val j-(pure b).val j else 0) +
                (if i=v then (pure c).val j-(pure b).val j else 0)) := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases hi : i=u
              · subst i; simp [B, huv]
              · by_cases hiv : i=v
                · subst i; simp [B, Ne.symm huv]
                · simp [B, hi, hiv]
            _ = _ := by simp [Finset.sum_add_distrib]
        rw [hh] at hb
        change (f B).val j = _
        rw [hb]
        dsimp [r]
        field_simp
        <;> ring
      have cross (a b c : Fin m) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
          (u v w : Fin n) (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v) :
          let p := mix a b hab (3*r/2) (by linarith) (by linarith)
          let pc := mix c b (Ne.symm hbc) (3*r/2) (by linarith) (by linarith)
          let P : Profile n m := fun i => if i=u then p else if i=v then pure c else pure b
          d pc (f P) < 3*r/4 := by
        dsimp only
        let t := 3*r/2
        let h := 3*r/4
        have ht : 0 ≤ t := by dsimp [t]; linarith
        have ht1 : t ≤ 1 := by dsimp [t]; linarith
        have hh : 0 ≤ h := by dsimp [h]; linarith
        have hh1 : h ≤ 1 := by dsimp [h]; linarith
        let p := mix a b hab t ht ht1
        let pc := mix c b (Ne.symm hbc) t ht ht1
        let P : Profile n m := fun i => if i=u then p else if i=v then pure c else pure b
        let B : Profile n m := fun i => if i=u then pure a else if i=v then pure c else pure b
        let q := f P
        have qb := base u v huv a b c
        change ∀ j, (f B).val j = _ at qb
        have dab : d p (f B) ≤ r := by
          apply (dle _ _ _).mpr
          intro j
          rw [qb]
          dsimp [p, mix, pure]
          by_cases hja : j=a
          · subst j; simp [hab, hac]; apply abs_le.mpr; dsimp [t]; constructor <;> linarith
          · by_cases hjb : j=b
            · subst j; simp [Ne.symm hab, hbc]; apply abs_le.mpr; dsimp [t]; constructor <;> linarith
            · by_cases hjc : j=c
              · subst j; simp [Ne.symm hac, Ne.symm hbc, abs_of_nonneg (le_of_lt hr)]
              · simp [hja, hjb, hjc]; linarith
        have dsp := sp u P B (by intro i hi; simp [P, B, hi])
        have hpu : P u = p := by simp [P]
        rw [hpu] at dsp
        have dqr : d p q ≤ r := le_trans dsp dab
        have cq := dc p q c
        simp [p, mix, Ne.symm hac, Ne.symm hbc, abs_of_nonneg (q.property.1 c)] at cq
        have cqr : q.val c ≤ r := le_trans cq dqr
        have st := structure_claim a b c hab hac hbc u v w huv hwu hwv t ht ht1
        change q.val a+q.val b+q.val c=1 ∧ (q.val c≤t → 1-t≤q.val b) at st
        have bq : 1-t ≤ q.val b := st.2 (by dsimp [t]; linarith)
        have cqh : h < q.val c := by
          by_contra hnch
          have ch : q.val c ≤ h := le_of_not_gt hnch
          let ph := mix a b hab h hh hh1
          let R : Profile n m := fun i => if i=u then ph else if i=v then pure c else pure b
          let C : Profile n m := fun i => if i=u then pure b else if i=v then pure c else pure b
          have dhq : d ph q ≤ h := by
            apply (dle _ _ _).mpr
            intro j
            by_cases hja : j=a
            · subst j
              simp [ph, mix, hab]
              apply abs_le.mpr
              have := q.property.1 a
              dsimp [h, t] at *
              constructor <;> linarith [q.property.1 c]
            · by_cases hjb : j=b
              · subst j
                simp [ph, mix, Ne.symm hab]
                apply abs_le.mpr
                dsimp [h, t] at *
                constructor <;> linarith [q.property.1 a, q.property.1 c]
              · by_cases hjc : j=c
                · subst j; simpa [ph, mix, Ne.symm hac, Ne.symm hbc, abs_of_nonneg (q.property.1 c)] using ch
                · rw [zero_other q a b c hab hac hbc st.1 j hja hjb hjc]
                  simpa [ph, mix, hja, hjb] using hh
          have dsr := sp u R P (by intro i hi; simp [R, P, hi])
          have hru : R u = ph := by simp [R]
          rw [hru] at dsr
          have drh : d ph (f R) ≤ h := le_trans dsr dhq
          have cr := dc ph (f R) c
          simp [ph, mix, Ne.symm hac, Ne.symm hbc, abs_of_nonneg ((f R).property.1 c)] at cr
          have str := structure_claim a b c hab hac hbc u v w huv hwu hwv h hh hh1
          change (f R).val a+(f R).val b+(f R).val c=1 ∧ ((f R).val c≤h → 1-h≤(f R).val b) at str
          have br : 1-h ≤ (f R).val b := str.2 (le_trans cr drh)
          have dsc := sp u C R (by intro i hi; simp [C, R, hi])
          have hcu : C u = pure b := by simp [C]
          rw [hcu, pure_d, pure_d] at dsc
          have cb := base u v huv b b c b
          change (f C).val b = _ at cb
          simp [pure, hbc] at cb
          dsimp [h] at br
          linarith
        change d pc q < h
        apply (dlt _ _ _).mpr
        intro j
        by_cases hja : j=a
        · subst j
          simp [pc, mix, hac, hab, abs_of_nonneg (q.property.1 a)]
          dsimp [t, h] at *
          linarith [st.1]
        · by_cases hjb : j=b
          · subst j
            simp [pc, mix, hbc]
            apply abs_lt.mpr
            dsimp [t, h] at *
            constructor <;> linarith [q.property.1 a, st.1]
          · by_cases hjc : j=c
            · subst j
              simp [pc, mix, Ne.symm hbc]
              apply abs_lt.mpr
              dsimp [t, h] at *
              constructor <;> linarith
            · rw [zero_other q a b c hab hac hbc st.1 j hja hjb hjc]
              simpa [pc, mix, hjb, hjc] using (show 0<h by dsimp [h]; linarith)
      let a : Fin m := ⟨0, by omega⟩
      let b : Fin m := ⟨1, by omega⟩
      let c : Fin m := ⟨2, by omega⟩
      let u : Fin n := ⟨0, by omega⟩
      let v : Fin n := ⟨1, by omega⟩
      let w : Fin n := ⟨2, by omega⟩
      have hab : a ≠ b := by simp [a,b,Fin.ext_iff]
      have hac : a ≠ c := by simp [a,c,Fin.ext_iff]
      have hbc : b ≠ c := by simp [b,c,Fin.ext_iff]
      have huv : u ≠ v := by simp [u,v,Fin.ext_iff]
      have hwu : w ≠ u := by simp [w,u,Fin.ext_iff]
      have hwv : w ≠ v := by simp [w,v,Fin.ext_iff]
      have ht : 0 ≤ 3*r/2 := by linarith
      have ht1 : 3*r/2 ≤ 1 := by linarith
      let pa := mix a b hab (3*r/2) ht ht1
      let pc := mix c b (Ne.symm hbc) (3*r/2) ht ht1
      let P1 : Profile n m := fun i => if i=u then pa else if i=v then pure c else pure b
      let P5 : Profile n m := fun i => if i=v then pc else if i=u then pure a else pure b
      let P6 : Profile n m := fun i => if i=u then pa else if i=v then pc else pure b
      have h1 := cross a b c hab hac hbc u v w huv hwu hwv
      change d pc (f P1) < 3*r/4 at h1
      have h5 := cross c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) v u w (Ne.symm huv) hwv hwu
      change d pa (f P5) < 3*r/4 at h5
      have s1 := sp v P6 P1 (by intro i hi; simp [P6, P1, hi])
      have hv : P6 v = pc := by simp [P6, Ne.symm huv]
      rw [hv] at s1
      have s5 := sp u P6 P5 (by
        intro i hi
        by_cases hiv : i=v
        · subst i; simp [P6, P5, Ne.symm huv]
        · simp [P6, P5, hi, hiv])
      have hu : P6 u = pa := by simp [P6]
      rw [hu] at s5
      have hca := dc pc (f P6) a
      have haa := dc pa (f P6) a
      simp [pc, mix, hac, hab, abs_of_nonneg ((f P6).property.1 a)] at hca
      simp [pa, mix, hab] at haa
      have hca' : (f P6).val a < 3*r/4 := lt_of_le_of_lt hca (lt_of_le_of_lt s1 h1)
      have haa' : |3*r/2-(f P6).val a| < 3*r/4 := lt_of_le_of_lt haa (lt_of_le_of_lt s5 h5)
      have := (abs_lt.mp haa').2
      linarith
