-- Prove2me | solution 1 for FamousTheorems.church_rosser_abstract_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:54:41.145782+00:00
-- url     : https://prove2.me/submissions/2db7fc41-8f61-4048-8db8-c22f04cd5b36

import Mathlib

theorem solution {α : Type*} {r : α → α → Prop} {a b c : α}
    (h : ∀ a b c, r a b → r a c → ∃ d, Relation.ReflGen r b d ∧ Relation.ReflTransGen r c d)
    (hab : Relation.ReflTransGen r a b) (hac : Relation.ReflTransGen r a c) :
    Relation.Join (Relation.ReflTransGen r) b c :=
  Relation.church_rosser h hab hac
